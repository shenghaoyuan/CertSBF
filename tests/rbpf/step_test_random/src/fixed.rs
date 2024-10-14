#![allow(clippy::arithmetic_side_effects)]
#![allow(unused)]

extern crate byteorder;
extern crate libc;
extern crate solana_rbpf;
extern crate test_utils;
extern crate thiserror;

use solana_rbpf::{
    assembler::assemble,
    error::ProgramResult,
    program::{BuiltinFunction, BuiltinProgram, FunctionRegistry},
    memory_region::MemoryRegion,
    vm::{Config, TestContextObject},
};
use test_utils::create_vm;
use std::sync::Arc;

use std::fs::File;
use std::io::{BufReader, BufRead};
use std::path::Path;

macro_rules! test_interpreter_step {
    (register, $function_registry:expr, $location:expr => $syscall_function:expr) => {
        $function_registry
            .register_function_hashed($location.as_bytes(), $syscall_function)
            .unwrap();
    };
    ($executable:expr, $register_map:expr, $mem:tt, $rx_index:expr) => {
        let mut mem = $mem;
        let mem_region = MemoryRegion::new_writable(&mut mem, 0x400000000); // ebpf::MM_INPUT_START
        let mut context_object = TestContextObject::new(0);
        create_vm!(
            vm,
            &$executable,
            &mut context_object,
            stack,
            heap,
            vec![mem_region],
            None
        );
        let result = vm.execute_step(&$executable, &$register_map, $rx_index);
        println!("Result: {:?}", result);
    };
}

macro_rules! test_interpreter_step_asm {
    ($source:tt, $register_map:expr, $mem:tt, $rx_index:expr) => {
        #[allow(unused_mut)]
        {
            let mut config = Config::default();
            config.enable_instruction_tracing = true;
            config.enable_instruction_meter = false;
            let function_registry = FunctionRegistry::<BuiltinFunction<TestContextObject>>::default();
            let loader = Arc::new(BuiltinProgram::new_loader(config, function_registry));
            let executable = assemble($source, loader).unwrap();
            test_interpreter_step!(executable, $register_map, $mem, $rx_index);
        }
    };
}
fn main() {
    let path_str = "~/data/rust_in.txt";
    let input_path = shellexpand::tilde(path_str).into_owned();
    let file = File::open(&input_path).expect("Cannot open input file");
    let reader = BufReader::new(file);

    let mut lines = reader.lines();
    while let Some(line) = lines.next() {
        let line = line.expect("Could not read line");

        if line.trim().is_empty() {
            continue;
        }

        if line.starts_with("Test Case Index:") {

            let mut register_values: Vec<u64> = Vec::new();
            for _ in 0..10 {
                let reg_line = lines.next().expect("Expected register value").expect("Could not read line");
                let reg_value = reg_line.trim_end_matches(',').trim();
                let reg_value = u64::from_str_radix(reg_value.trim_start_matches("0x"), 16).expect("Invalid register value");
                register_values.push(reg_value);
            }

            let register_map: Vec<(String, i64)> = register_values
                .iter()
                .enumerate()
                .map(|(i, &val)| (format!("r{}", i), val as i64))
                .collect();

            let mut data_map: Vec<u8> = Vec::new();
            let data_line = lines.next().expect("Expected data map").expect("Could not read line");
            let data_values = data_line.trim().split(',');
            for data_value in data_values {
                if data_value.is_empty() {
                    continue;
                }
                let data_value = u8::from_str_radix(data_value.trim_start_matches("0x"), 16).expect("Invalid data value");
                data_map.push(data_value);
            }

            let rx_index_line = lines.next().expect("Expected RX_index").expect("Could not read line");
            let rx_index = rx_index_line.trim().parse::<usize>().expect("Invalid RX_index");
 
            let assembly_line = lines.next().expect("Expected assembly instruction").expect("Could not read line");
            let assembly_code = assembly_line.trim();

            test_interpreter_step_asm!(
                assembly_code,
                &register_map,
                data_map,
                rx_index
            );
        }
    }
}
