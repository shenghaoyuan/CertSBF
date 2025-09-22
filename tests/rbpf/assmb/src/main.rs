#![allow(mismatched_lifetime_syntaxes)]


use solana_rbpf::assembler::assemble;
use solana_rbpf::program::BuiltinProgram;
use solana_rbpf::vm::TestContextObject;
use std::sync::Arc;
use regex::Regex;

struct TestCase {
    dis: String,           
    assembly_code: String,  
    lm_std: Vec<i64>,        
    fuel: i64,             
    result_expected: i64,  
}

fn assemble_to_bytecode(assembly_code: &str) -> Result<Vec<u8>, String> {
    let executable = assemble::<TestContextObject>(
        assembly_code,
        Arc::new(BuiltinProgram::new_mock()),
    ).map_err(|e| e.to_string())?; 

    let program = executable.get_text_bytes().1;

    Ok(program.to_vec())
}


fn parse_rust_test_case(rust_test: &str) -> Option<TestCase> {
    let re = Regex::new(
        r#"(?s)fn\s+(\w+)\s*\(\)\s*\{\s*test_interpreter_and_jit_asm!\(\s*"([\s\S]*?)",\s*\[([\s\S]*?)\],\s*\(\),\s*TestContextObject::new\((\d+)\),\s*ProgramResult::Ok\((0x[0-9a-fA-F]+)\),"#
    ).unwrap();

    if let Some(caps) = re.captures(rust_test) {
        let dis = caps.get(1)?.as_str().to_string();
        let assembly_code = caps.get(2)?.as_str().to_string();
        let lm_std_str = caps.get(3)?.as_str().trim();
        let lm_std: Vec<i64> = if lm_std_str.is_empty() {
            Vec::new()
        } else {
            lm_std_str.split(',')
                .map(|s| s.trim())
                .filter_map(|s| {
                    if s.starts_with("0x") || s.starts_with("0X") {
                        i64::from_str_radix(&s[2..], 16).ok()
                    } else {
                        s.parse::<i64>().ok()
                    }
                })
                .collect()
        };
        let fuel: i64 = caps.get(4)?.as_str().parse().ok()?;
        let result_expected_str = caps.get(5)?.as_str();
        let result_expected = if result_expected_str.starts_with("0x") || result_expected_str.starts_with("0X") {
            i64::from_str_radix(&result_expected_str[2..], 16).ok()?
        } else {
            result_expected_str.parse::<i64>().ok()?
        };

        Some(TestCase {
            dis,
            assembly_code,
            lm_std,
            fuel,
            result_expected,
        })
    } else {
        None
    }
}


fn main() {

    let rust_test_cases = vec![
r#"
fn test_step() {
    test_interpreter_and_jit_asm!(
        "
        mov32 r0, 1
        exit",
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x1),
    );
}

"#,

    ];

    for rust_test in rust_test_cases {
        match parse_rust_test_case(rust_test) {
            Some(test) => {

                println!("(*\n{}\n*)", test.assembly_code.trim());

                match assemble_to_bytecode(&test.assembly_code) {
                    Ok(bytecode) => {

                        let lp_std: Vec<String> = bytecode.iter()
                            .map(|byte| format!("0x{:02x}L", byte))
                            .collect();
                        let lp_std_str = lp_std.join("; ");

                        let lm_std: Vec<String> = test.lm_std.iter()
                            .map(|byte| format!("0x{:x}L", byte))
                            .collect();
                        let lm_std_str = if lm_std.is_empty() {
                            "".to_string()
                        } else {
                            lm_std.join("; ")
                        };

                        println!("{{");
                        println!("  dis = \"{}\";", test.dis);
                        println!("  lp_std = [{}];", lp_std_str);
                        println!("  lm_std = [{}];", lm_std_str);
                        println!("  lc_std = [];");
                        println!("  v = 2L;");
                        println!("  fuel = {}L;", test.fuel);
                        println!("  result_expected = 0x{:x}L;", test.result_expected);
                        println!("}};");
                        println!();
                    },
                    Err(error) => {
                        eprintln!("Error assembling test '{}': {}", test.dis, error);
                    },
                }
            },
            None => {
                eprintln!("Failed to parse Rust test case.");
            }
        }
    }
}
