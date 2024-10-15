use solana_rbpf::assembler::assemble;
use solana_rbpf::program::{BuiltinFunction, BuiltinProgram, FunctionRegistry,SBPFVersion};
use solana_rbpf::memory_region::MemoryRegion;
use solana_rbpf::vm::{Config, TestContextObject};
use test_utils::create_vm;
use rand::Rng;
use serde::{Serialize, Deserialize};
use serde_json;
use std::fs::{File, create_dir_all};
use std::io::BufWriter;
use std::path::Path;
use std::sync::Arc;
use std::env;

#[derive(Serialize, Deserialize)]
struct TestCase {
    dis: String,
    lp_std: Vec<String>,
    lr_std: Vec<String>,
    lm_std: Vec<String>,
    lc_std: Vec<String>,
    v: String,
    fuel: String,
    index: String,
    ipc: String,
    result_expected: String,
}

#[derive(Clone, Copy)]
enum InstructionVersion {
    V1,
    V2,
}

#[derive(Clone, Copy)]
enum InstructionType {
    AluBinary,
    AluPQR,
    AluUnary,
    LoadReg,
    LoadDwImm,
    StoreReg,
    StoreImm,
    JumpUnconditional,
    JumpConditional,
    Endian
}

#[derive(Clone, Copy)]
enum InstructionLength {
    OneOperand,
    TwoOperands,
    ThreeOperands,
}

struct InstructionSet {
    version: InstructionVersion,
    length: InstructionLength,
    class: InstructionType,
    instructions: &'static [&'static str],
}

fn assemble_to_bytecode(assembly_code: &str) -> Result<Vec<u8>, String> {
    let executable = assemble::<TestContextObject>(
        assembly_code,
        Arc::new(BuiltinProgram::new_mock()),
    ).map_err(|e| e.to_string())?;

    let program = executable.get_text_bytes().1;

    Ok(program.to_vec())
}

fn generate_and_process_test_cases(num_cases: usize) -> Vec<TestCase> {

    //let MM_INPUT_START::u64 = 0x400000000;
    let instruction_sets = [
        InstructionSet {
            version: InstructionVersion::V1,
            length: InstructionLength::OneOperand,
            class: InstructionType::AluUnary,
            instructions: &[
                "neg", "neg64",
                "neg32", 
            ],
        },
        InstructionSet {
            version: InstructionVersion::V1,
            length: InstructionLength::TwoOperands,
            class: InstructionType::AluPQR,
            instructions: &[
                "mul", "div", "mod", 
                "mul32", "div32", "mod32",
                
            ],
        },
        InstructionSet {
            version: InstructionVersion::V2,
            length: InstructionLength::TwoOperands,
            class: InstructionType::AluPQR,
            instructions: &[
                "udiv", "udiv64", "lmul", "lmul64", "uhmul", "uhmul64", "shmul", "shmul64",
                "udiv64", "urem", "urem64", "urem32", "sdiv", "sdiv64", "sdiv32", "srem", "srem64","srem32"
            ],
        },
        InstructionSet {
            version: InstructionVersion::V2,
            length: InstructionLength::TwoOperands,
            class: InstructionType::AluBinary,
            instructions: &[
                "add", "sub", "or", "and", "lsh", "rsh", "xor", "mov", "arsh",
                "add32", "sub32", "or32", "and32", "lsh32", "rsh32", "xor32", "mov32", "arsh32", 

            ],
        },
        InstructionSet {
            version: InstructionVersion::V2,
            length: InstructionLength::TwoOperands,
            class: InstructionType::LoadReg,
            instructions: &[
                "ldxb", "ldxh", "ldxw", "ldxdw"
            ],
        },
        InstructionSet {
            version: InstructionVersion::V1,
            length: InstructionLength::TwoOperands,
            class: InstructionType::LoadDwImm,
            instructions: &[
                "lddw"
            ],
        },
        InstructionSet {
            version: InstructionVersion::V2,
            length: InstructionLength::TwoOperands,
            class: InstructionType::StoreImm,
            instructions: &[
                "stb", "sth", "stw", "stdw"
            ],
        },
        InstructionSet {
            version: InstructionVersion::V2,
            length: InstructionLength::TwoOperands,
            class: InstructionType::StoreReg,
            instructions: &[
                "stxb", "stxh", "stxw", "stxdw"
            ],
        },
        InstructionSet {
            version: InstructionVersion::V2,
            length: InstructionLength::ThreeOperands,
            class: InstructionType::JumpConditional,
            instructions: &[
                "jeq", "jgt", "jge", "jlt", "jle", "jset", "jne", "jsgt", "jsge", "jslt", "jsle", //ja
            ],
        },
        InstructionSet {
            version: InstructionVersion::V2,
            length: InstructionLength::OneOperand,
            class: InstructionType::JumpUnconditional,
            instructions: &[
                "ja"
            ],
        },
        InstructionSet {
            version: InstructionVersion::V1,
            length: InstructionLength::OneOperand,
            class: InstructionType::Endian,
            instructions: &[
                "be16", "be32", "be64",
                "le16", "le32", "le64",
            ],
        },
    ];

    let mut rng = rand::thread_rng();

    let mut test_cases = Vec::new();

    for _ in 0..num_cases {

        let instruction_set = &instruction_sets[rng.gen_range(0..instruction_sets.len())];
        let op = instruction_set.instructions[rng.gen_range(0..instruction_set.instructions.len())];
        let version = instruction_set.version;
        let length = instruction_set.length;
        let class = instruction_set.class;

        let istore = match class {
            InstructionType::StoreReg | InstructionType::StoreImm => true,
            _ => false,
        };

        let isload = match class {
            InstructionType::LoadReg => true,
            _ => false,
        };

        let mut registers: Vec<i64> = Vec::new();
        for i in 0..10 {
            let value: i64 = if i == 0 { 0 } else { rng.gen::<i64>() };
            registers.push(value);
        }

        let data_map: Vec<u8> = if istore | isload {
            (0..110).collect::<Vec<u8>>()
        }else {
            Vec::new()
        };

        let rx_index = rng.gen_range(0..10);
        let rx = format!("r{}", rx_index);

        let is_register = rng.gen_bool(0.5);
        
        let operand = if is_register {
            let mut ry_index = rng.gen_range(0..10);
            if let InstructionType::AluPQR = class {
                while registers[ry_index] == 0 {
                    ry_index = rng.gen_range(0..10);
                }
            }
            format!("r{}", ry_index)
        } else {
            let mut imm = rng.gen_range(i32::MIN as i64..=i32::MAX as i64);
            match class {
                InstructionType::AluPQR => while imm == 0 {
                    imm = rng.gen_range(i32::MIN as i64..=i32::MAX as i64);
                },
                InstructionType::LoadDwImm => imm = rng.gen_range(i64::MIN..=i64::MAX),
                _ => {}
            }
            format!("{}", imm)
        };

        let offset: i64 = rng.gen_range(i16::MIN as i64..=i16::MAX as i64);
        let ofs = format!("{}", offset);

        let assembly_code = match length {
            InstructionLength::OneOperand => {
                match class {
                    InstructionType::AluUnary => format!("{} {}", op, rx),
                    InstructionType::Endian => format!("{} {}", op, rx),
                    InstructionType::JumpUnconditional => format!("{} {}", op, ofs),
                    _ => {
                        println!("Match Error"); 
                        continue
                    }
                }
            },
            InstructionLength::TwoOperands => {
                match class {
                    InstructionType::AluBinary | InstructionType::AluPQR => format!("{} {}, {}", op, rx, operand),
                    InstructionType::StoreReg => 
                    {
                        let d: i64 = rng.gen_range(0..100);
                        let dis = format!("{}", d);                

                        let ry_index = rng.gen_range(1..10);
                        let ry = format!("r{}", ry_index);
                        format!("{} [r0+{}], {} ldxdw {}, [r0+{}]", op, dis, ry, rx, dis)
                    },
                    InstructionType::StoreImm => 
                    {
                        let d: i64 = rng.gen_range(0..100);
                        let dis = format!("{}", d);                

                        let imm: i64 = rng.gen_range(i32::MIN as i64..=i32::MAX as i64);
                        format!("{} [r0+{}], {} ldxdw {}, [r0+{}]", op, dis, imm, rx, dis)
                    },
                    InstructionType::LoadReg => 
                    {
                        let d: i64 = rng.gen_range(0..100);
                        let dis = format!("{}", d); 

                        format!("{} {}, [r0+{}]", op, rx, dis)
                    },
                    InstructionType::LoadDwImm => 
                    {
                        let dwi: i64 = rng.gen_range(i64::MIN as i64..=i64::MAX as i64);
                        let dw_imm = format!("{}", dwi); 

                        format!("{} {}, {}", op, rx, dw_imm)
                    },
                    _ => {
                        println!("Match Error"); 
                        continue
                    }
                }
            }
            InstructionLength::ThreeOperands => format!("{} {}, {}, {}", op, rx, operand, ofs),
        };

        //println!("{:?}",assembly_code);

        match assemble_to_bytecode(&assembly_code) {
            Ok(bytecode) => {

                let lp_std: Vec<String> = bytecode.iter()
                    .map(|byte| format!("0x{:02X}", byte))
                    .collect();

                let lr_std: Vec<String> = registers.iter()
                    .map(|val| format!("0x{:016X}", val))
                    .collect();

                let lm_std: Vec<String> = data_map.iter()
                    .map(|val| format!("0x{:02X}", val))
                    .collect();


                let register_map: Vec<(String, i64)> = registers
                    .iter()
                    .enumerate()
                    .map(|(i, &val)| (format!("r{}", i), val))
                    .collect();

                let mut mem = data_map.clone();
                let mem_region = MemoryRegion::new_writable(&mut mem, 0x400000000);

                let config = match version {
                    InstructionVersion::V1 => Config {
                        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
                        enable_instruction_tracing: false,
                        enable_instruction_meter: false,
                        ..Config::default()
                    },
                    InstructionVersion::V2 => Config {
                        enable_instruction_tracing: false,
                        enable_instruction_meter: false,
                        ..Config::default()
                    },
                };

                let function_registry = FunctionRegistry::<BuiltinFunction<TestContextObject>>::default();
                let loader = Arc::new(BuiltinProgram::new_loader(config, function_registry));

                match assemble::<TestContextObject>(&assembly_code, loader.clone()) {
                    Ok(executable) => {
                        let mut context_object = TestContextObject::new(0);
                        create_vm!(
                            vm,
                            &executable,
                            &mut context_object,
                            stack,
                            heap,
                            vec![mem_region],
                            None
                        );
                        let result = vm.execute_step(&executable, &register_map, rx_index, istore, isload);
                        if !(result.0) {
                            println!("{}", assembly_code);
                            println!("{:?}", bytecode);
                            continue
                        };
                        let test_case = TestCase {
                            dis: assembly_code.clone(),
                            lp_std,
                            lr_std,
                            lm_std,
                            lc_std: Vec::new(),
                            v: match version {
                                InstructionVersion::V1 => format!("0x{:X}", 1),
                                InstructionVersion::V2 => format!("0x{:X}", 2),
                            },
                            fuel: match class {
                                InstructionType::StoreReg | InstructionType::StoreImm => format!("0x{:X}", 2),
                                _ => format!("0x{:X}", 1),
                            },
                            index: format!("0x{:X}", rx_index),
                            ipc: format!("0x{:X}", result.3),
                            result_expected: format!("0x{:X}", result.2),
                        };
                        test_cases.push(test_case);
                    }
                    Err(error) => {
                        println!("Assembly Error: {}", error);
                        continue;
                    }
                }
            }
            Err(error) => {
                println!("Bytecode Assembly Error: {}", error);
                continue;
            }
        }
    }

    test_cases
}
fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();
    let num_test_cases = args.get(1).map_or(100, |x| x.parse::<usize>().unwrap_or(100));

    let test_cases = generate_and_process_test_cases(num_test_cases);

    let output_path_str = "../../data/ocaml_in.json";
    let output_path = shellexpand::tilde(output_path_str).into_owned();

    if let Some(dir_path) = Path::new(&output_path).parent() {
        if !dir_path.exists() {
            create_dir_all(dir_path)?;
        }
    }

    let file = File::create(&output_path)?;
    let writer = BufWriter::new(file);

    serde_json::to_writer_pretty(writer, &test_cases)?;

    println!("Successfully generated {} random test cases.", num_test_cases);
    Ok(())
}


