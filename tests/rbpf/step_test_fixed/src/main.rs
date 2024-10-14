use solana_rbpf::assembler::assemble;
use solana_rbpf::program::{BuiltinFunction, BuiltinProgram, FunctionRegistry};
use solana_rbpf::memory_region::MemoryRegion;
use solana_rbpf::vm::{Config, TestContextObject};
use test_utils::create_vm;
use serde::{Serialize, Deserialize};
use serde_json;
use std::fs::File;
use std::io::BufReader;
use std::sync::Arc;

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
}

fn assemble_to_bytecode(assembly_code: &str) -> Result<Vec<u8>, String> {
    let executable = assemble::<TestContextObject>(
        assembly_code,
        Arc::new(BuiltinProgram::new_mock()),
    ).map_err(|e| e.to_string())?;

    let program = executable.get_text_bytes().1;

    Ok(program.to_vec())
}

fn read_test_cases(file_path: &str) -> Result<Vec<TestCase>, Box<dyn std::error::Error>> {
    let file = File::open(file_path)?;
    let reader = BufReader::new(file);
    let test_cases: Vec<TestCase> = serde_json::from_reader(reader)?;
    Ok(test_cases)
}

fn hex_to_u8(hex_str: &str) -> Result<u8, std::num::ParseIntError> {
    u8::from_str_radix(hex_str.trim_start_matches("0x"), 16)
}

fn hex_to_u64(hex_str: &str) -> Result<u64, std::num::ParseIntError> {
    u64::from_str_radix(hex_str.trim_start_matches("0x"), 16)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input_path = "../../data/rust_in.json";
    let test_cases = read_test_cases(input_path)?;

    for (i, test_case) in test_cases.iter().enumerate() {

        let assembly_code = &test_case.dis;

        // Assemble the assembly code to bytecode
        let _bytecode = match assemble_to_bytecode(&test_case.dis) {
            Ok(bytes) => bytes,
            Err(e) => {
                println!("Test case {}: Assembly error: {}", i, e);
                continue;
            }
        };

        // Convert lp_std from hex strings to bytes
        let _lp_std_bytes: Vec<u8> = match test_case.lp_std.iter().map(|s| hex_to_u8(s)).collect() {
            Ok(bytes) => bytes,
            Err(e) => {
                println!("Test case {}: lp_std parse error: {}", i, e);
                continue;
            }
        };

        // Convert lr_std from hex strings to u64 and create register_map
        let register_map: Vec<(String, i64)> = match test_case.lr_std.iter().enumerate().map(|(idx, s)| {
            hex_to_u64(s).map(|val| (format!("r{}", idx), val as i64))
        }).collect::<Result<Vec<(String, i64)>, _>>() {
            Ok(map) => map,
            Err(e) => {
                println!("Test case {}: lr_std parse error: {}", i, e);
                continue;
            }
        };

        // Convert lm_std from hex strings to bytes
        let mem_bytes: Vec<u8> = match test_case.lm_std.iter().map(|s| hex_to_u8(s)).collect() {
            Ok(bytes) => bytes,
            Err(e) => {
                println!("Test case {}: lm_std parse error: {}", i, e);
                continue;
            }
        };

        // Convert index from hex string to u64
        let rx_index = match hex_to_u64(&test_case.index) {
            Ok(val) => val as usize,
            Err(e) => {
                println!("Test case {}: index parse error: {}", i, e);
                continue;
            }
        };
        let mut mem = mem_bytes.clone();
        let mem_region = MemoryRegion::new_writable(&mut mem, 0x400000000);

        let mut config = Config::default();
        config.enable_instruction_tracing = false;
        config.enable_instruction_meter = false;
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

                let result = vm.execute_step(&executable, &register_map, rx_index);
                println!("Result: {:X?}", result);   
            }
            Err(error) => {
                println!("error: {}", error);
                continue;
            }
        }
    }

    Ok(())
}
