#![allow(clippy::arithmetic_side_effects)]
#![allow(unused)]
#![cfg(all(feature = "jit", not(target_os = "windows"), target_arch = "x86_64"))]
// Copyright 2020 Solana Maintainers <maintainers@solana.com>
//
// Licensed under the Apache License, Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0> or
// the MIT license <http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

extern crate byteorder;
extern crate libc;
extern crate solana_rbpf;
extern crate test_utils;
extern crate thiserror;

use byteorder::{ByteOrder, LittleEndian};
#[cfg(all(not(windows), target_arch = "x86_64"))]
use rand::{rngs::SmallRng, RngCore, SeedableRng};
use solana_rbpf::{
    assembler::assemble,
    declare_builtin_function, ebpf,
    elf::Executable,
    error::{EbpfError, ProgramResult},
    memory_region::{AccessType, MemoryMapping, MemoryRegion},
    program::{BuiltinFunction, BuiltinProgram, FunctionRegistry, SBPFVersion},
    static_analysis::Analysis,
    syscalls,
    verifier::RequisiteVerifier,
    vm::{Config, ContextObject, TestContextObject},
};
use std::{fs::File, io::Read, sync::Arc};
use test_utils::{
    assert_error, create_vm, PROG_TCP_PORT_80, TCP_SACK_ASM, TCP_SACK_MATCH, TCP_SACK_NOMATCH,
};

const INSTRUCTION_METER_BUDGET: u64 = 1024;

macro_rules! test_interpreter_and_jit {
    (register, $function_registry:expr, $location:expr => $syscall_function:expr) => {
        $function_registry
            .register_function_hashed($location.as_bytes(), $syscall_function)
            .unwrap();
    };
    ($executable:expr, $mem:tt, $context_object:expr, $expected_result:expr $(,)?) => {
        test_interpreter_and_jit!(true, $executable, $mem, $context_object, $expected_result)
    };
    ($verify:literal, $executable:expr, $mem:tt, $context_object:expr, $expected_result:expr $(,)?) => {
        let expected_instruction_count = $context_object.get_remaining();
        #[allow(unused_mut)]
        let mut context_object = $context_object;
        let expected_result = format!("{:?}", $expected_result);
        if !expected_result.contains("ExceededMaxInstructions") {
            context_object.remaining = INSTRUCTION_METER_BUDGET;
        }
        if $verify {
            $executable.verify::<RequisiteVerifier>().unwrap();
        }
        println!("Running interpreter_jit");
        let (instruction_count_interpreter, interpreter_final_pc, _tracer_interpreter) = {
            let mut mem = $mem;
            let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
            let mut context_object = context_object.clone();
            create_vm!(
                vm,
                &$executable,
                &mut context_object,
                stack,
                heap,
                vec![mem_region],
                None
            );
            let (instruction_count_interpreter, result) = vm.execute_program(&$executable, true);
            assert_eq!(
                format!("{:?}", result),
                expected_result,
                "Unexpected result for Interpreter"
            );
            (
                instruction_count_interpreter,
                vm.registers[11],
                vm.context_object_pointer.clone(),
            )
        };
        #[cfg(all(feature = "jit", not(target_os = "windows"), target_arch = "x86_64"))]
        {
            #[allow(unused_mut)]
            let compilation_result = $executable.jit_compile();
            let mut mem = $mem;
            let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
            create_vm!(
                vm,
                &$executable,
                &mut context_object,
                stack,
                heap,
                vec![mem_region],
                None
            );
            match compilation_result {
                Err(err) => assert_eq!(
                    format!("{:?}", err),
                    expected_result,
                    "Unexpected result for JIT compilation"
                ),
                Ok(()) => {
                    let (instruction_count_jit, result) = vm.execute_program(&$executable, false);
                    let tracer_jit = &vm.context_object_pointer;
                    if !TestContextObject::compare_trace_log(&_tracer_interpreter, tracer_jit) {
                        let analysis = Analysis::from_executable(&$executable).unwrap();
                        let stdout = std::io::stdout();
                        analysis
                            .disassemble_trace_log(
                                &mut stdout.lock(),
                                &_tracer_interpreter.trace_log,
                            )
                            .unwrap();
                        analysis
                            .disassemble_trace_log(&mut stdout.lock(), &tracer_jit.trace_log)
                            .unwrap();
                        panic!();
                    }
                    assert_eq!(
                        format!("{:?}", result),
                        expected_result,
                        "Unexpected result for JIT"
                    );
                    assert_eq!(
                        instruction_count_interpreter, instruction_count_jit,
                        "Interpreter and JIT instruction meter diverged",
                    );
                    assert_eq!(
                        interpreter_final_pc, vm.registers[11],
                        "Interpreter and JIT instruction final PC diverged",
                    );
                }
            }
        }
        if $executable.get_config().enable_instruction_meter {
            assert_eq!(
                instruction_count_interpreter, expected_instruction_count,
                "Instruction meter did not consume expected amount"
            );
        }
    };
}


macro_rules! test_interpreter_and_interpreter2_time {
    (register, $function_registry:expr, $location:expr => $syscall_function:expr) => {
        $function_registry
            .register_function_hashed($location.as_bytes(), $syscall_function)
            .unwrap();
    };
    ($executable:expr, $mem:tt, $context_object:expr, $expected_result:expr $(,)?) => {
        test_interpreter_and_interpreter2_time!(true, $executable, $mem, $context_object, $expected_result)
    };
    ($verify:literal, $executable:expr, $mem:tt, $context_object:expr, $expected_result:expr $(,)?) => {{
        use std::time::Instant;
        let expected_instruction_count = $context_object.get_remaining();
        
        #[allow(unused_mut)]
        let mut context_object = $context_object;
        let expected_result = format!("{:?}", $expected_result);
        if !expected_result.contains("ExceededMaxInstructions") {
            context_object.remaining = INSTRUCTION_METER_BUDGET;
        }
        if $verify {
            $executable.verify::<RequisiteVerifier>().unwrap();
        }
        {
            let mut mem = $mem;
            let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
            let mut context_clone = context_object.clone();
            
            create_vm!(
                vm,
                &$executable,
                &mut context_clone,
                stack,
                heap,
                vec![mem_region],
                None
            );
            
            let (instruction_count_interpreter, result) = vm.execute_program(&$executable, true);
            assert_eq!(
                format!("{:?}", result),
                expected_result,
                "Unexpected result for Interpreter"
            );
            if $executable.get_config().enable_instruction_meter {
                assert_eq!(
                    instruction_count_interpreter, expected_instruction_count,
                    "Instruction meter did not consume expected amount"
                );
            }
        }
        {
            let mut mem = $mem;
            let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
            let mut context_clone = context_object.clone();
            create_vm!(
                vm,
                &$executable,
                &mut context_clone,
                stack,
                heap,
                vec![mem_region],
                None
            );
            let (instruction_count_interpreter2, result2) = vm.execute_program(&$executable, true);
            assert_eq!(
                format!("{:?}", result2),
                expected_result,
                "Unexpected result for Interpreter2"
            );
            if $executable.get_config().enable_instruction_meter {
                assert_eq!(
                    instruction_count_interpreter2, expected_instruction_count,
                    "Instruction meter did not consume expected amount for Interpreter2"
                );
            }
        }
        
        let iterations = 1_000;
        let mut total_time_interpreter = std::time::Duration::new(0, 0);
        let mut total_time_interpreter2 = std::time::Duration::new(0, 0);
        //println!("Running Interpreter1");
        for _ in 0..iterations {
            let mut mem = $mem;
            let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
            let mut context_clone = context_object.clone();
            
            create_vm!(
                vm,
                &$executable,
                &mut context_clone,
                stack,
                heap,
                vec![mem_region],
                None
            );
            
            let start = Instant::now();
            vm.execute_program(&$executable, true);
            let duration = start.elapsed();
            total_time_interpreter += duration;
        }
        //println!("Running Interpreter2");
        for _ in 0..iterations {
            let mut mem = $mem;
            let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
            let mut context_clone = context_object.clone();
            
            create_vm!(
                vm,
                &$executable,
                &mut context_clone,
                stack,
                heap,
                vec![mem_region],
                None
            );
            let start = Instant::now();
            vm.execute_program(&$executable, true);
            let duration = start.elapsed();
            total_time_interpreter2 += duration;
        }
        println!(
            "Total execution time for Interpreter ({} iterations): {:?}",
            iterations, total_time_interpreter
        );
        println!(
            "Total execution time for Interpreter2 ({} iterations): {:?}",
            iterations, total_time_interpreter2
        );
        assert!(
            total_time_interpreter2 < total_time_interpreter,
            "Interpreter2 is not faster than Interpreter"
        );
    }};
}


macro_rules! test_interpreter_and_interpreter2_asm {
    ($source:tt, $config:expr, $mem:tt, ($($location:expr => $syscall_function:expr),* $(,)?), $context_object:expr, $expected_result:expr $(,)?) => {
        #[allow(unused_mut)]
        {
            let mut config = $config;
            config.enable_instruction_tracing = true;
            let mut function_registry = FunctionRegistry::<BuiltinFunction<TestContextObject>>::default();
            $(test_interpreter_and_interpreter2_time!(register, function_registry, $location => $syscall_function);)*
            let loader = Arc::new(BuiltinProgram::new_loader(config, function_registry));
            let mut executable = assemble($source, loader).unwrap();
            test_interpreter_and_interpreter2_time!(executable, $mem, $context_object, $expected_result);
        }
    };
    ($source:tt, $mem:tt, ($($location:expr => $syscall_function:expr),* $(,)?), $context_object:expr, $expected_result:expr $(,)?) => {
        #[allow(unused_mut)]
        {
            test_interpreter_and_interpreter2_asm!($source, Config::default(), $mem, ($($location => $syscall_function),*), $context_object, $expected_result);
        }
    };
}

// BPF_ALU : Arithmetic and Logic

#[test]
fn test_mov() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r1, 1
        mov32 r0, r1
        exit",
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_mov32_imm_large() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, -1
        exit",
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0xffffffff),
    );
}

#[test]
fn test_mov_large() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r1, -1
        mov32 r0, r1
        exit",
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0xffffffff),
    );
}

#[test]
fn test_bounce() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 1
        mov r6, r0
        mov r7, r6
        mov r8, r7
        mov r9, r8
        mov r0, r9
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_add32() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 2
        add32 r0, 1
        add32 r0, r1
        exit",
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Ok(0x3),
    );
}
#[test]
fn test_alu32_arithmetic() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 1
        mov32 r2, 2
        mov32 r3, 3
        mov32 r4, 4
        mov32 r5, 5
        mov32 r6, 6
        mov32 r7, 7
        mov32 r8, 8
        mov32 r9, 9
        sub32 r0, 13
        sub32 r0, r1
        add32 r0, 23
        add32 r0, r7
        lmul32 r0, 7
        lmul32 r0, r3
        udiv32 r0, 2
        udiv32 r0, r4
        exit",
        [],
        (),
        TestContextObject::new(19),
        ProgramResult::Ok(110),
    );
}

#[test]
fn test_alu64_arithmetic() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        mov r1, 1
        mov r2, 2
        mov r3, 3
        mov r4, 4
        mov r5, 5
        mov r6, 6
        mov r7, 7
        mov r8, 8
        mov r9, 9
        sub r0, 13
        sub r0, r1
        add r0, 23
        add r0, r7
        lmul r0, 7
        lmul r0, r3
        udiv r0, 2
        udiv r0, r4
        exit",
        [],
        (),
        TestContextObject::new(19),
        ProgramResult::Ok(110),
    );
}

#[test]
fn test_lmul128() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        mov r2, 30
        mov r3, 0
        mov r4, 20
        mov r5, 0
        lmul64 r3, r4
        lmul64 r5, r2
        add64 r5, r3
        mov64 r0, r2
        rsh64 r0, 0x20
        mov64 r3, r4
        rsh64 r3, 0x20
        mov64 r6, r3
        lmul64 r6, r0
        add64 r5, r6
        lsh64 r4, 0x20
        rsh64 r4, 0x20
        mov64 r6, r4
        lmul64 r6, r0
        lsh64 r2, 0x20
        rsh64 r2, 0x20
        lmul64 r4, r2
        mov64 r0, r4
        rsh64 r0, 0x20
        add64 r0, r6
        mov64 r6, r0
        rsh64 r6, 0x20
        add64 r5, r6
        lmul64 r3, r2
        lsh64 r0, 0x20
        rsh64 r0, 0x20
        add64 r0, r3
        mov64 r2, r0
        rsh64 r2, 0x20
        add64 r5, r2
        stxdw [r1+0x8], r5
        lsh64 r0, 0x20
        lsh64 r4, 0x20
        rsh64 r4, 0x20
        or64 r0, r4
        stxdw [r1+0x0], r0
        exit",
        [0; 16],
        (),
        TestContextObject::new(42),
        ProgramResult::Ok(600),
    );
}

#[test]
fn test_alu32_logic() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 1
        mov32 r2, 2
        mov32 r3, 3
        mov32 r4, 4
        mov32 r5, 5
        mov32 r6, 6
        mov32 r7, 7
        mov32 r8, 8
        or32 r0, r5
        or32 r0, 0xa0
        and32 r0, 0xa3
        mov32 r9, 0x91
        and32 r0, r9
        lsh32 r0, 22
        lsh32 r0, r8
        rsh32 r0, 19
        rsh32 r0, r7
        xor32 r0, 0x03
        xor32 r0, r2
        exit",
        [],
        (),
        TestContextObject::new(21),
        ProgramResult::Ok(0x11),
    );
}

#[test]
fn test_alu64_logic() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        mov r1, 1
        mov r2, 2
        mov r3, 3
        mov r4, 4
        mov r5, 5
        mov r6, 6
        mov r7, 7
        mov r8, 8
        or r0, r5
        or r0, 0xa0
        and r0, 0xa3
        mov r9, 0x91
        and r0, r9
        lsh r0, 32
        lsh r0, 22
        lsh r0, r8
        rsh r0, 32
        rsh r0, 19
        rsh r0, r7
        xor r0, 0x03
        xor r0, r2
        exit",
        [],
        (),
        TestContextObject::new(23),
        ProgramResult::Ok(0x11),
    );
}

#[test]
fn test_arsh32_high_shift() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 8
        mov32 r1, 0x00000001
        hor64 r1, 0x00000001
        arsh32 r0, r1
        exit",
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Ok(0x4),
    );
}

#[test]
fn test_arsh32_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0xf8
        lsh32 r0, 28
        arsh32 r0, 16
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0xffff8000),
    );
}

#[test]
fn test_arsh32_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0xf8
        mov32 r1, 16
        lsh32 r0, 28
        arsh32 r0, r1
        exit",
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Ok(0xffff8000),
    );
}

#[test]
fn test_arsh64() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 1
        lsh r0, 63
        arsh r0, 55
        mov32 r1, 5
        arsh r0, r1
        exit",
        [],
        (),
        TestContextObject::new(6),
        ProgramResult::Ok(0xfffffffffffffff8),
    );
}

#[test]
fn test_lsh64_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0x1
        mov r7, 4
        lsh r0, r7
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x10),
    );
}

#[test]
fn test_rhs32_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        xor r0, r0
        add r0, -1
        rsh32 r0, 8
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x00ffffff),
    );
}

#[test]
fn test_rsh64_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0x10
        mov r7, 4
        rsh r0, r7
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_be16() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxh r0, [r1]
        be16 r0
        exit",
        [0x11, 0x22],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1122),
    );
}

#[test]
fn test_be16_high() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1]
        be16 r0
        exit",
        [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1122),
    );
}

#[test]
fn test_be32() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxw r0, [r1]
        be32 r0
        exit",
        [0x11, 0x22, 0x33, 0x44],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x11223344),
    );
}

#[test]
fn test_be32_high() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1]
        be32 r0
        exit",
        [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x11223344),
    );
}

#[test]
fn test_be64() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1]
        be64 r0
        exit",
        [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1122334455667788),
    );
}

// BPF_LD : Loads

#[test]
fn test_hor64() {
    test_interpreter_and_interpreter2_asm!(
        "
        hor64 r0, 0x10203040
        hor64 r0, 0x01020304
        exit",
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1122334400000000),
    );
}

#[test]
fn test_ldxb() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxb r0, [r1+2]
        exit",
        [0xaa, 0xbb, 0x11, 0xcc, 0xdd],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x11),
    );
}

#[test]
fn test_ldxh() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxh r0, [r1+2]
        exit",
        [0xaa, 0xbb, 0x11, 0x22, 0xcc, 0xdd],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x2211),
    );
}

#[test]
fn test_ldxw() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxw r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0x11, 0x22, 0x33, 0x44, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x44332211),
    );
}

#[test]
fn test_ldxh_same_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        sth [r0], 0x1234
        ldxh r0, [r0]
        exit",
        [0xff, 0xff],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x1234),
    );
}

#[test]
fn test_lldxdw() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, //
            0x77, 0x88, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x8877665544332211),
    );
}

#[test]
fn test_err_ldxdw_oob() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1+6]
        exit",
        [
            0xaa, 0xbb, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, //
            0x77, 0x88, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(1),
        ProgramResult::Err(EbpfError::AccessViolation(
            AccessType::Load,
            0x400000006,
            8,
            "input"
        )),
    );
}

#[test]
fn test_err_ldxdw_nomem() {
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1+6]
        exit",
        [],
        (),
        TestContextObject::new(1),
        ProgramResult::Err(EbpfError::AccessViolation(
            AccessType::Load,
            0x400000006,
            8,
            "input"
        )),
    );
}

#[test]
fn test_ldxb_all() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        ldxb r9, [r0+0]
        lsh r9, 0
        ldxb r8, [r0+1]
        lsh r8, 4
        ldxb r7, [r0+2]
        lsh r7, 8
        ldxb r6, [r0+3]
        lsh r6, 12
        ldxb r5, [r0+4]
        lsh r5, 16
        ldxb r4, [r0+5]
        lsh r4, 20
        ldxb r3, [r0+6]
        lsh r3, 24
        ldxb r2, [r0+7]
        lsh r2, 28
        ldxb r1, [r0+8]
        lsh r1, 32
        ldxb r0, [r0+9]
        lsh r0, 36
        or r0, r1
        or r0, r2
        or r0, r3
        or r0, r4
        or r0, r5
        or r0, r6
        or r0, r7
        or r0, r8
        or r0, r9
        exit",
        [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, //
            0x08, 0x09, //
        ],
        (),
        TestContextObject::new(31),
        ProgramResult::Ok(0x9876543210),
    );
}

#[test]
fn test_ldxh_all() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        ldxh r9, [r0+0]
        be16 r9
        lsh r9, 0
        ldxh r8, [r0+2]
        be16 r8
        lsh r8, 4
        ldxh r7, [r0+4]
        be16 r7
        lsh r7, 8
        ldxh r6, [r0+6]
        be16 r6
        lsh r6, 12
        ldxh r5, [r0+8]
        be16 r5
        lsh r5, 16
        ldxh r4, [r0+10]
        be16 r4
        lsh r4, 20
        ldxh r3, [r0+12]
        be16 r3
        lsh r3, 24
        ldxh r2, [r0+14]
        be16 r2
        lsh r2, 28
        ldxh r1, [r0+16]
        be16 r1
        lsh r1, 32
        ldxh r0, [r0+18]
        be16 r0
        lsh r0, 36
        or r0, r1
        or r0, r2
        or r0, r3
        or r0, r4
        or r0, r5
        or r0, r6
        or r0, r7
        or r0, r8
        or r0, r9
        exit",
        [
            0x00, 0x00, 0x00, 0x01, 0x00, 0x02, 0x00, 0x03, //
            0x00, 0x04, 0x00, 0x05, 0x00, 0x06, 0x00, 0x07, //
            0x00, 0x08, 0x00, 0x09, //
        ],
        (),
        TestContextObject::new(41),
        ProgramResult::Ok(0x9876543210),
    );
}

#[test]
fn test_ldxh_all2() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        ldxh r9, [r0+0]
        be16 r9
        ldxh r8, [r0+2]
        be16 r8
        ldxh r7, [r0+4]
        be16 r7
        ldxh r6, [r0+6]
        be16 r6
        ldxh r5, [r0+8]
        be16 r5
        ldxh r4, [r0+10]
        be16 r4
        ldxh r3, [r0+12]
        be16 r3
        ldxh r2, [r0+14]
        be16 r2
        ldxh r1, [r0+16]
        be16 r1
        ldxh r0, [r0+18]
        be16 r0
        or r0, r1
        or r0, r2
        or r0, r3
        or r0, r4
        or r0, r5
        or r0, r6
        or r0, r7
        or r0, r8
        or r0, r9
        exit",
        [
            0x00, 0x01, 0x00, 0x02, 0x00, 0x04, 0x00, 0x08, //
            0x00, 0x10, 0x00, 0x20, 0x00, 0x40, 0x00, 0x80, //
            0x01, 0x00, 0x02, 0x00, //
        ],
        (),
        TestContextObject::new(31),
        ProgramResult::Ok(0x3ff),
    );
}

#[test]
fn test_ldxw_all() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        ldxw r9, [r0+0]
        be32 r9
        ldxw r8, [r0+4]
        be32 r8
        ldxw r7, [r0+8]
        be32 r7
        ldxw r6, [r0+12]
        be32 r6
        ldxw r5, [r0+16]
        be32 r5
        ldxw r4, [r0+20]
        be32 r4
        ldxw r3, [r0+24]
        be32 r3
        ldxw r2, [r0+28]
        be32 r2
        ldxw r1, [r0+32]
        be32 r1
        ldxw r0, [r0+36]
        be32 r0
        or r0, r1
        or r0, r2
        or r0, r3
        or r0, r4
        or r0, r5
        or r0, r6
        or r0, r7
        or r0, r8
        or r0, r9
        exit",
        [
            0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, //
            0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x08, //
            0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, //
            0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x08, 0x00, //
            0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, //
        ],
        (),
        TestContextObject::new(31),
        ProgramResult::Ok(0x030f0f),
    );
}

#[test]
fn test_stb() {
    test_interpreter_and_interpreter2_asm!(
        "
        stb [r1+2], 0x11
        ldxb r0, [r1+2]
        exit",
        [0xaa, 0xbb, 0xff, 0xcc, 0xdd],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x11),
    );
}

#[test]
fn test_sth() {
    test_interpreter_and_interpreter2_asm!(
        "
        sth [r1+2], 0x2211
        ldxh r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0xff, 0xff, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x2211),
    );
}

#[test]
fn test_stw() {
    test_interpreter_and_interpreter2_asm!(
        "
        stw [r1+2], 0x44332211
        ldxw r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0xff, 0xff, 0xff, 0xff, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x44332211),
    );
}

#[test]
fn test_stdw() {
    test_interpreter_and_interpreter2_asm!(
        "
        stdw [r1+2], 0x44332211
        ldxdw r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, //
            0xff, 0xff, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x44332211),
    );
}

#[test]
fn test_stxb() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r2, 0x11
        stxb [r1+2], r2
        ldxb r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0xff, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x11),
    );
}

#[test]
fn test_stxh() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r2, 0x2211
        stxh [r1+2], r2
        ldxh r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0xff, 0xff, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x2211),
    );
}

#[test]
fn test_stxw() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r2, 0x44332211
        stxw [r1+2], r2
        ldxw r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0xff, 0xff, 0xff, 0xff, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x44332211),
    );
}

#[test]
fn test_stxdw() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r2, -2005440939
        lsh r2, 32
        or r2, 0x44332211
        stxdw [r1+2], r2
        ldxdw r0, [r1+2]
        exit",
        [
            0xaa, 0xbb, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, //
            0xff, 0xff, 0xcc, 0xdd, //
        ],
        (),
        TestContextObject::new(6),
        ProgramResult::Ok(0x8877665544332211),
    );
}

#[test]
fn test_stxb_all() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0xf0
        mov r2, 0xf2
        mov r3, 0xf3
        mov r4, 0xf4
        mov r5, 0xf5
        mov r6, 0xf6
        mov r7, 0xf7
        mov r8, 0xf8
        stxb [r1], r0
        stxb [r1+1], r2
        stxb [r1+2], r3
        stxb [r1+3], r4
        stxb [r1+4], r5
        stxb [r1+5], r6
        stxb [r1+6], r7
        stxb [r1+7], r8
        ldxdw r0, [r1]
        be64 r0
        exit",
        [
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, //
        ],
        (),
        TestContextObject::new(19),
        ProgramResult::Ok(0xf0f2f3f4f5f6f7f8),
    );
}

#[test]
fn test_stxb_all2() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        mov r1, 0xf1
        mov r9, 0xf9
        stxb [r0], r1
        stxb [r0+1], r9
        ldxh r0, [r0]
        be16 r0
        exit",
        [0xff, 0xff],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(0xf1f9),
    );
}

#[test]
fn test_stxb_chain() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, r1
        ldxb r9, [r0+0]
        stxb [r0+1], r9
        ldxb r8, [r0+1]
        stxb [r0+2], r8
        ldxb r7, [r0+2]
        stxb [r0+3], r7
        ldxb r6, [r0+3]
        stxb [r0+4], r6
        ldxb r5, [r0+4]
        stxb [r0+5], r5
        ldxb r4, [r0+5]
        stxb [r0+6], r4
        ldxb r3, [r0+6]
        stxb [r0+7], r3
        ldxb r2, [r0+7]
        stxb [r0+8], r2
        ldxb r1, [r0+8]
        stxb [r0+9], r1
        ldxb r0, [r0+9]
        exit",
        [
            0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, //
            0x00, 0x00, //
        ],
        (),
        TestContextObject::new(21),
        ProgramResult::Ok(0x2a),
    );
}

// BPF_JMP : Branches

#[test]
fn test_exit_capped() {
    test_interpreter_and_interpreter2_asm!(
        "
        exit",
        [],
        (),
        TestContextObject::new(0),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_exit_without_value() {
    test_interpreter_and_interpreter2_asm!(
        "
        exit",
        [],
        (),
        TestContextObject::new(1),
        ProgramResult::Ok(0x0),
    );
}

#[test]
fn test_exit() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        exit",
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x0),
    );
}

#[test]
fn test_early_exit() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 3
        exit
        mov r0, 4
        exit",
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x3),
    );
}

#[test]
fn test_ja() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 1
        ja +1
        mov r0, 2
        exit",
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jeq_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0xa
        jeq r1, 0xb, +4
        mov32 r0, 1
        mov32 r1, 0xb
        jeq r1, 0xb, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jeq_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0xa
        mov32 r2, 0xb
        jeq r1, r2, +4
        mov32 r0, 1
        mov32 r1, 0xb
        jeq r1, r2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jge_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0xa
        jge r1, 0xb, +4
        mov32 r0, 1
        mov32 r1, 0xc
        jge r1, 0xb, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jge_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0xa
        mov32 r2, 0xb
        jge r1, r2, +4
        mov32 r0, 1
        mov32 r1, 0xb
        jge r1, r2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jle_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 5
        jle r1, 4, +1
        jle r1, 6, +1
        exit
        jle r1, 5, +1
        exit
        mov32 r0, 1
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jle_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        mov r1, 5
        mov r2, 4
        mov r3, 6
        jle r1, r2, +2
        jle r1, r1, +1
        exit
        jle r1, r3, +1
        exit
        mov r0, 1
        exit",
        [],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jgt_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 5
        jgt r1, 6, +2
        jgt r1, 5, +1
        jgt r1, 4, +1
        exit
        mov32 r0, 1
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jgt_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        mov r1, 5
        mov r2, 6
        mov r3, 4
        jgt r1, r2, +2
        jgt r1, r1, +1
        jgt r1, r3, +1
        exit
        mov r0, 1
        exit",
        [],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jlt_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 5
        jlt r1, 4, +2
        jlt r1, 5, +1
        jlt r1, 6, +1
        exit
        mov32 r0, 1
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jlt_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        mov r1, 5
        mov r2, 4
        mov r3, 6
        jlt r1, r2, +2
        jlt r1, r1, +1
        jlt r1, r3, +1
        exit
        mov r0, 1
        exit",
        [],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jne_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0xb
        jne r1, 0xb, +4
        mov32 r0, 1
        mov32 r1, 0xa
        jne r1, 0xb, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jne_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0xb
        mov32 r2, 0xb
        jne r1, r2, +4
        mov32 r0, 1
        mov32 r1, 0xa
        jne r1, r2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jset_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0x7
        jset r1, 0x8, +4
        mov32 r0, 1
        mov32 r1, 0x9
        jset r1, 0x8, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jset_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov32 r1, 0x7
        mov32 r2, 0x8
        jset r1, r2, +4
        mov32 r0, 1
        mov32 r1, 0x9
        jset r1, r2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jsge_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -2
        jsge r1, -1, +5
        jsge r1, 0, +4
        mov32 r0, 1
        mov r1, -1
        jsge r1, -1, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jsge_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -2
        mov r2, -1
        mov32 r3, 0
        jsge r1, r2, +5
        jsge r1, r3, +4
        mov32 r0, 1
        mov r1, r2
        jsge r1, r2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(10),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jsle_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -2
        jsle r1, -3, +1
        jsle r1, -1, +1
        exit
        mov32 r0, 1
        jsle r1, -2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jsle_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -1
        mov r2, -2
        mov32 r3, 0
        jsle r1, r2, +1
        jsle r1, r3, +1
        exit
        mov32 r0, 1
        mov r1, r2
        jsle r1, r2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(10),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jsgt_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -2
        jsgt r1, -1, +4
        mov32 r0, 1
        mov32 r1, 0
        jsgt r1, -1, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jsgt_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -2
        mov r2, -1
        jsgt r1, r2, +4
        mov32 r0, 1
        mov32 r1, 0
        jsgt r1, r2, +1
        mov32 r0, 2
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jslt_imm() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -2
        jslt r1, -3, +2
        jslt r1, -2, +1
        jslt r1, -1, +1
        exit
        mov32 r0, 1
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_jslt_reg() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 0
        mov r1, -2
        mov r2, -3
        mov r3, -1
        jslt r1, r1, +2
        jslt r1, r2, +1
        jslt r1, r3, +1
        exit
        mov32 r0, 1
        exit",
        [],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0x1),
    );
}

// Call Stack

#[test]
fn test_stack1() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r1, 51
        stdw [r10-16], 0xab
        stdw [r10-8], 0xcd
        and r1, 1
        lsh r1, 3
        mov r2, r10
        add r2, r1
        ldxdw r0, [r2-16]
        exit",
        [],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0xcd),
    );
}

#[test]
fn test_stack2() {
    test_interpreter_and_interpreter2_asm!(
        "
        stb [r10-4], 0x01
        stb [r10-3], 0x02
        stb [r10-2], 0x03
        stb [r10-1], 0x04
        mov r1, r10
        mov r2, 0x4
        sub r1, r2
        syscall bpf_mem_frob
        mov r1, 0
        ldxb r2, [r10-4]
        ldxb r3, [r10-3]
        ldxb r4, [r10-2]
        ldxb r5, [r10-1]
        syscall bpf_gather_bytes
        xor r0, 0x2a2a2a2a
        exit",
        [],
        (
            "bpf_mem_frob" => syscalls::SyscallMemFrob::vm,
            "bpf_gather_bytes" => syscalls::SyscallGatherBytes::vm,
        ),
        TestContextObject::new(16),
        ProgramResult::Ok(0x01020304),
    );
}

#[test]
fn test_string_stack() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r1, 0x78636261
        stxw [r10-8], r1
        mov r6, 0x0
        stxb [r10-4], r6
        stxb [r10-12], r6
        mov r1, 0x79636261
        stxw [r10-16], r1
        mov r1, r10
        add r1, -8
        mov r2, r1
        syscall bpf_str_cmp
        mov r1, r0
        mov r0, 0x1
        lsh r1, 0x20
        rsh r1, 0x20
        jne r1, 0x0, +11
        mov r1, r10
        add r1, -8
        mov r2, r10
        add r2, -16
        syscall bpf_str_cmp
        mov r1, r0
        lsh r1, 0x20
        rsh r1, 0x20
        mov r0, 0x1
        jeq r1, r6, +1
        mov r0, 0x0
        exit",
        [],
        (
            "bpf_str_cmp" => syscalls::SyscallStrCmp::vm,
        ),
        TestContextObject::new(28),
        ProgramResult::Ok(0x0),
    );
}

#[test]
fn test_err_dynamic_stack_out_of_bound() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V2,
        max_call_depth: 3,
        ..Config::default()
    };

    // The stack goes from MM_STACK_START + config.stack_size() to MM_STACK_START

    // Check that accessing MM_STACK_START - 1 fails
    test_interpreter_and_interpreter2_asm!(
        "
        stb [r10-0x3001], 0
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(1),
        ProgramResult::Err(EbpfError::AccessViolation(
            AccessType::Store,
            ebpf::MM_STACK_START - 1,
            1,
            "program"
        )),
    );

    // Check that accessing MM_STACK_START + expected_stack_len fails
    test_interpreter_and_interpreter2_asm!(
        "
        stb [r10], 0
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(1),
        ProgramResult::Err(EbpfError::AccessViolation(
            AccessType::Store,
            ebpf::MM_STACK_START + config.stack_size() as u64,
            1,
            "stack"
        )),
    );
}

#[test]
fn test_err_dynamic_stack_ptr_overflow() {
    // See the comment in CallFrames::resize_stack() for the reason why it's
    // safe to let the stack pointer overflow

    // stack_ptr -= stack_ptr + 1
    test_interpreter_and_interpreter2_asm!(
        "
        add r11, -0x7FFFFFFF
        add r11, -0x7FFFFFFF
        add r11, -0x7FFFFFFF
        add r11, -0x7FFFFFFF
        add r11, -0x40005
        call function_foo
        exit
        function_foo:
        stb [r10], 0
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Err(EbpfError::AccessViolation(
            AccessType::Store,
            u64::MAX,
            1,
            "unknown"
        )),
    );
}

#[test]
fn test_dynamic_stack_frames_empty() {
    let config = Config::default();

    // Check that unless explicitly resized the stack doesn't grow
    test_interpreter_and_interpreter2_asm!(
        "
        call function_foo
        exit
        function_foo:
        mov r0, r10
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(ebpf::MM_STACK_START + config.stack_size() as u64),
    );
}

#[test]
fn test_dynamic_frame_ptr() {
    let config = Config::default();

    // Check that upon entering a function (foo) the frame pointer is advanced
    // to the top of the stack
    test_interpreter_and_interpreter2_asm!(
        "
        add r11, -8
        call function_foo
        exit
        function_foo:
        mov r0, r10
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Ok(ebpf::MM_STACK_START + config.stack_size() as u64 - 8),
    );

    // And check that when exiting a function (foo) the caller's frame pointer
    // is restored
    test_interpreter_and_interpreter2_asm!(
        "
        add r11, -8
        call function_foo
        mov r0, r10
        exit
        function_foo:
        exit
        ",
        config.clone(),
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Ok(ebpf::MM_STACK_START + config.stack_size() as u64),
    );
}

#[test]
fn test_entrypoint_exit() {
    // With fixed frames we used to exit the entrypoint when we reached an exit
    // instruction and the stack size was 1 * config.stack_frame_size, which
    // meant that we were in the entrypoint's frame.  With dynamic frames we
    // can't infer anything from the stack size so we track call depth
    // explicitly. Make sure exit still works with both fixed and dynamic
    // frames.
    for highest_sbpf_version in [SBPFVersion::V1, SBPFVersion::V2] {
        let config = Config {
            enabled_sbpf_versions: SBPFVersion::V1..=highest_sbpf_version,
            ..Config::default()
        };

        // This checks that when foo exits we don't stop execution even if the
        // stack is empty (stack size and call depth are decoupled)
        test_interpreter_and_interpreter2_asm!(
            "
            entrypoint:
            call function_foo
            mov r0, 42
            exit
            function_foo:
            mov r0, 12
            exit",
            config,
            [],
            (),
            TestContextObject::new(5),
            ProgramResult::Ok(42),
        );
    }
}

#[test]
fn test_stack_call_depth_tracking() {
    for highest_sbpf_version in [SBPFVersion::V1, SBPFVersion::V2] {
        let config = Config {
            enabled_sbpf_versions: SBPFVersion::V1..=highest_sbpf_version,
            max_call_depth: 2,
            ..Config::default()
        };

        // Given max_call_depth=2, make sure that two sibling calls don't
        // trigger CallDepthExceeded. In other words ensure that we correctly
        // pop frames in the interpreter and decrement
        // EnvironmentStackSlotDepth on ebpf::EXIT in the jit.
        test_interpreter_and_interpreter2_asm!(
            "
            call function_foo
            call function_foo
            exit
            function_foo:
            exit
            ",
            config.clone(),
            [],
            (),
            TestContextObject::new(5),
            ProgramResult::Ok(0),
        );

        // two nested calls should trigger CallDepthExceeded instead
        test_interpreter_and_interpreter2_asm!(
            "
            entrypoint:
            call function_foo
            exit
            function_foo:
            call function_bar
            exit
            function_bar:
            exit
            ",
            config,
            [],
            (),
            TestContextObject::new(2),
            ProgramResult::Err(EbpfError::CallDepthExceeded),
        );
    }
}


#[test]
fn test_bpf_to_bpf_scratch_registers() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r6, 0x11
        mov64 r7, 0x22
        mov64 r8, 0x44
        mov64 r9, 0x88
        call function_foo
        mov64 r0, r6
        add64 r0, r7
        add64 r0, r8
        add64 r0, r9
        exit
        function_foo:
        mov64 r6, 0x00
        mov64 r7, 0x00
        mov64 r8, 0x00
        mov64 r9, 0x00
        exit",
        [],
        (),
        TestContextObject::new(15),
        ProgramResult::Ok(0xFF),
    );
}

#[test]
fn test_syscall_parameter_on_stack() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, r10
        add64 r1, -0x100
        mov64 r2, 0x1
        syscall bpf_syscall_string
        mov64 r0, 0x0
        exit",
        [],
        (
            "bpf_syscall_string" => syscalls::SyscallString::vm,
        ),
        TestContextObject::new(6),
        ProgramResult::Ok(0),
    );
}

#[test]
fn test_callx() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r0, 0x0
        mov64 r8, 0x1
        lsh64 r8, 0x20
        or64 r8, 0x30
        callx r8
        exit
        function_foo:
        mov64 r0, 0x2A
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(42),
    );
}

#[test]
fn test_err_callx_unregistered() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r0, 0x0
        mov64 r8, 0x1
        lsh64 r8, 0x20
        or64 r8, 0x30
        callx r8
        exit
        mov64 r0, 0x2A
        exit",
        [],
        (),
        TestContextObject::new(6),
        ProgramResult::Err(EbpfError::UnsupportedInstruction),
    );
}

#[test]
fn test_err_callx_oob_low() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r0, 0x3
        callx r0
        exit",
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Err(EbpfError::CallOutsideTextSegment),
    );
}

#[test]
fn test_err_callx_oob_high() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r0, -0x1
        lsh64 r0, 0x20
        or64 r0, 0x3
        callx r0
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Err(EbpfError::CallOutsideTextSegment),
    );
}

#[test]
fn test_bpf_to_bpf_depth() {
    for max_call_depth in [20usize, Config::default().max_call_depth] {
        let config = Config {
            max_call_depth,
            ..Config::default()
        };
        test_interpreter_and_interpreter2_asm!(
            "
            ldxb r1, [r1]
            add64 r1, -2
            call function_foo
            exit
            function_foo:
            jeq r1, 0, +2
            add64 r1, -1
            call function_foo
            exit",
            config.clone(),
            [max_call_depth as u8],
            (),
            TestContextObject::new(max_call_depth as u64 * 4 - 2),
            ProgramResult::Ok(0),
        );
        // The instruction count is lower here because all the `exit`s never run
        test_interpreter_and_interpreter2_asm!(
            "
            ldxb r1, [r1]
            add64 r1, -2
            call function_foo
            exit
            function_foo:
            jeq r1, 0, +2
            add64 r1, -1
            call function_foo
            exit",
            config,
            [max_call_depth as u8 + 1],
            (),
            TestContextObject::new(max_call_depth as u64 * 3),
            ProgramResult::Err(EbpfError::CallDepthExceeded),
        );
    }
}

#[test]
fn test_err_reg_stack_depth() {
    for max_call_depth in [20usize, Config::default().max_call_depth] {
        let config = Config {
            max_call_depth,
            ..Config::default()
        };
        test_interpreter_and_interpreter2_asm!(
            "
            mov64 r0, 0x1
            lsh64 r0, 0x20
            callx r0
            exit",
            config,
            [],
            (),
            TestContextObject::new(max_call_depth as u64 * 3),
            ProgramResult::Err(EbpfError::CallDepthExceeded),
        );
    }
}

// CALL_IMM : Syscalls

/* TODO: syscalls::trash_registers needs asm!().
// https://github.com/rust-lang/rust/issues/72016
#[test]
fn test_call_save() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r6, 0x1
        mov64 r7, 0x20
        mov64 r8, 0x300
        mov64 r9, 0x4000
        call 0
        mov64 r0, 0x0
        or64 r0, r6
        or64 r0, r7
        or64 r0, r8
        or64 r0, r9
        exit",
        [],
        (
            0 => syscalls::trash_registers,
        ),
        { |_vm, res: ProgramResult| { res.unwrap() == 0 } }
    );
}*/

#[test]
fn test_err_syscall_string() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, 0x0
        syscall bpf_syscall_string
        mov64 r0, 0x0
        exit",
        [72, 101, 108, 108, 111],
        (
            "bpf_syscall_string" => syscalls::SyscallString::vm,
        ),
        TestContextObject::new(2),
        ProgramResult::Err(EbpfError::SyscallError(Box::new(EbpfError::AccessViolation(AccessType::Load, 0, 0, "unknown")))),
    );
}

#[test]
fn test_syscall_string() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r2, 0x5
        syscall bpf_syscall_string
        mov64 r0, 0x0
        exit",
        [72, 101, 108, 108, 111],
        (
            "bpf_syscall_string" => syscalls::SyscallString::vm,
        ),
        TestContextObject::new(4),
        ProgramResult::Ok(0),
    );
}

#[test]
fn test_syscall() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, 0xAA
        mov64 r2, 0xBB
        mov64 r3, 0xCC
        mov64 r4, 0xDD
        mov64 r5, 0xEE
        syscall bpf_syscall_u64
        mov64 r0, 0x0
        exit",
        [],
        (
            "bpf_syscall_u64" => syscalls::SyscallU64::vm,
        ),
        TestContextObject::new(8),
        ProgramResult::Ok(0),
    );
}

#[test]
fn test_call_gather_bytes() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r1, 1
        mov r2, 2
        mov r3, 3
        mov r4, 4
        mov r5, 5
        syscall bpf_gather_bytes
        exit",
        [],
        (
            "bpf_gather_bytes" => syscalls::SyscallGatherBytes::vm,
        ),
        TestContextObject::new(7),
        ProgramResult::Ok(0x0102030405),
    );
}

#[test]
fn test_call_memfrob() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r6, r1
        add r1, 2
        mov r2, 4
        syscall bpf_mem_frob
        ldxdw r0, [r6]
        be64 r0
        exit",
        [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, //
        ],
        (
            "bpf_mem_frob" => syscalls::SyscallMemFrob::vm,
        ),
        TestContextObject::new(7),
        ProgramResult::Ok(0x102292e2f2c0708),
    );
}

declare_builtin_function!(
    /// For test_nested_vm_syscall()
    SyscallNestedVm,
    fn rust(
        _context_object: &mut TestContextObject,
        depth: u64,
        throw: u64,
        _arg3: u64,
        _arg4: u64,
        _arg5: u64,
        _memory_mapping: &mut MemoryMapping,
    ) -> Result<u64, Box<dyn std::error::Error>> {
        let (result, expected_result): (Result<u64, Box<dyn std::error::Error>>, ProgramResult) =
            if throw == 0 {
                (Result::Ok(42), ProgramResult::Ok(42))
            } else {
                (
                    Result::Err(Box::new(EbpfError::CallDepthExceeded)),
                    ProgramResult::Err(EbpfError::SyscallError(Box::new(
                        EbpfError::CallDepthExceeded,
                    ))),
                )
            };
        #[allow(unused_mut)]
        if depth > 0 {
            let mut function_registry =
                FunctionRegistry::<BuiltinFunction<TestContextObject>>::default();
            function_registry
                .register_function_hashed(*b"nested_vm_syscall", SyscallNestedVm::vm)
                .unwrap();
            let loader = BuiltinProgram::new_loader(Config::default(), function_registry);
            let mem = [depth as u8 - 1, throw as u8];
            let mut executable = assemble::<TestContextObject>(
                "
                ldxb r2, [r1+1]
                ldxb r1, [r1]
                syscall nested_vm_syscall
                exit",
                Arc::new(loader),
            )
            .unwrap();
            test_interpreter_and_jit!(
                executable,
                mem,
                TestContextObject::new(if throw == 0 { 4 } else { 3 }),
                expected_result,
            );
        }
        result
    }
);

// Instruction Meter Limit

#[test]
fn test_tight_infinite_loop_conditional() {
    test_interpreter_and_interpreter2_asm!(
        "
        jsge r0, r0, -1
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_tight_infinite_loop_unconditional() {
    test_interpreter_and_interpreter2_asm!(
        "
        ja -1
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_tight_infinite_recursion() {
    test_interpreter_and_interpreter2_asm!(
        "
        entrypoint:
        mov64 r3, 0x41414141
        call entrypoint
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_tight_infinite_recursion_callx() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r8, 0x1
        lsh64 r8, 0x20
        or64 r8, 0x28
        call function_foo
        exit
        function_foo:
        mov64 r3, 0x41414141
        callx r8
        exit",
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_instruction_count_syscall() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r2, 0x5
        syscall bpf_syscall_string
        mov64 r0, 0x0
        exit",
        [72, 101, 108, 108, 111],
        (
            "bpf_syscall_string" => syscalls::SyscallString::vm,
        ),
        TestContextObject::new(4),
        ProgramResult::Ok(0),
    );
}

#[test]
fn test_err_instruction_count_syscall_capped() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r2, 0x5
        syscall bpf_syscall_string
        mov64 r0, 0x0
        exit",
        [72, 101, 108, 108, 111],
        (
            "bpf_syscall_string" => syscalls::SyscallString::vm,
        ),
        TestContextObject::new(3),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_non_terminate_early() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r6, 0x0
        mov64 r1, 0x0
        mov64 r2, 0x0
        mov64 r3, 0x0
        mov64 r4, 0x0
        mov64 r5, r6
        callx r6
        add64 r6, 0x1
        ja -0x8
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Err(EbpfError::CallOutsideTextSegment),
    );
}

#[test]
fn test_err_non_terminate_capped() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r6, 0x0
        mov64 r1, 0x0
        mov64 r2, 0x0
        mov64 r3, 0x0
        mov64 r4, 0x0
        mov64 r5, r6
        syscall bpf_trace_printf
        add64 r6, 0x1
        ja -0x8
        exit",
        [],
        (
            "bpf_trace_printf" => syscalls::SyscallTracePrintf::vm,
        ),
        TestContextObject::new(7),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r6, 0x0
        mov64 r1, 0x0
        mov64 r2, 0x0
        mov64 r3, 0x0
        mov64 r4, 0x0
        mov64 r5, r6
        syscall bpf_trace_printf
        add64 r6, 0x1
        ja -0x8
        exit",
        [],
        (
            "bpf_trace_printf" => syscalls::SyscallTracePrintf::vm,
        ),
        TestContextObject::new(1000),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_err_capped_before_exception() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, 0x0
        mov64 r2, 0x0
        add64 r0, 0x0
        add64 r0, 0x0
        udiv64 r1, r2
        add64 r0, 0x0
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );

    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, 0x0
        mov64 r2, 0x0
        add64 r0, 0x0
        add64 r0, 0x0
        callx r2
        add64 r0, 0x0
        exit",
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_err_exit_capped() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, 0x1
        lsh64 r1, 0x20
        or64 r1, 0x28
        callx r1
        exit
        function_foo:
        exit
        ",
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, 0x1
        lsh64 r1, 0x20
        or64 r1, 0x28
        callx r1
        exit
        function_foo:
        mov r0, r0
        exit
        ",
        [],
        (),
        TestContextObject::new(6),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        call 1
        exit
        mov r0, r0
        exit
        ",
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_far_jumps() {
    test_interpreter_and_interpreter2_asm!(
        "
        call function_c
        exit
        function_a:
        exit
        function_b:
        .fill 1024, 0x0F
        exit
        function_c:
        mov32 r1, 0x00000010
        hor64 r1, 0x00000001
        callx r1
        exit",
        [],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0),
    );
}

// Symbols and Relocation

#[test]
fn test_symbol_relocation() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, r10
        add64 r1, -0x1
        mov64 r2, 0x1
        syscall bpf_syscall_string
        mov64 r0, 0x0
        exit",
        [72, 101, 108, 108, 111],
        (
            "bpf_syscall_string" => syscalls::SyscallString::vm,
        ),
        TestContextObject::new(6),
        ProgramResult::Ok(0),
    );
}

#[test]
fn test_err_call_unresolved() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };

    test_interpreter_and_interpreter2_asm!(
        "
        mov r1, 1
        mov r2, 2
        mov r3, 3
        mov r4, 4
        mov r5, 5
        syscall Unresolved
        mov64 r0, 0x0
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(6),
        ProgramResult::Err(EbpfError::UnsupportedInstruction),
    );
}

// Programs

#[test]
fn test_lmul_loop() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0x7
        add r1, 0xa
        lsh r1, 0x20
        rsh r1, 0x20
        jeq r1, 0x0, +4
        mov r0, 0x7
        lmul r0, 0x7
        add r1, -1
        jne r1, 0x0, -3
        exit",
        [],
        (),
        TestContextObject::new(37),
        ProgramResult::Ok(0x75db9c97),
    );
}

#[test]
fn test_prime() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r1, 67
        mov r0, 0x1
        mov r2, 0x2
        jgt r1, 0x2, +4
        ja +10
        add r2, 0x1
        mov r0, 0x1
        jge r2, r1, +7
        mov r3, r1
        udiv r3, r2
        lmul r3, r2
        mov r4, r1
        sub r4, r3
        mov r0, 0x0
        jne r4, 0x0, -10
        exit",
        [],
        (),
        TestContextObject::new(655),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_subnet() {
    test_interpreter_and_interpreter2_asm!(
        "
        mov r2, 0xe
        ldxh r3, [r1+12]
        jne r3, 0x81, +2
        mov r2, 0x12
        ldxh r3, [r1+16]
        and r3, 0xffff
        jne r3, 0x8, +5
        add r1, r2
        mov r0, 0x1
        ldxw r1, [r1+16]
        and r1, 0xffffff
        jeq r1, 0x1a8c0, +1
        mov r0, 0x0
        exit",
        [
            0x00, 0x00, 0xc0, 0x9f, 0xa0, 0x97, 0x00, 0xa0, //
            0xcc, 0x3b, 0xbf, 0xfa, 0x08, 0x00, 0x45, 0x10, //
            0x00, 0x3c, 0x46, 0x3c, 0x40, 0x00, 0x40, 0x06, //
            0x73, 0x1c, 0xc0, 0xa8, 0x01, 0x02, 0xc0, 0xa8, //
            0x01, 0x01, 0x06, 0x0e, 0x00, 0x17, 0x99, 0xc5, //
            0xa0, 0xec, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x02, //
            0x7d, 0x78, 0xe0, 0xa3, 0x00, 0x00, 0x02, 0x04, //
            0x05, 0xb4, 0x04, 0x02, 0x08, 0x0a, 0x00, 0x9c, //
            0x27, 0x24, 0x00, 0x00, 0x00, 0x00, 0x01, 0x03, //
            0x03, 0x00, //
        ],
        (),
        TestContextObject::new(11),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_tcp_port80_match() {
    test_interpreter_and_interpreter2_asm!(
        PROG_TCP_PORT_80,
        [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x06, //
            0x07, 0x08, 0x09, 0x0a, 0x08, 0x00, 0x45, 0x00, //
            0x00, 0x56, 0x00, 0x01, 0x00, 0x00, 0x40, 0x06, //
            0xf9, 0x4d, 0xc0, 0xa8, 0x00, 0x01, 0xc0, 0xa8, //
            0x00, 0x02, 0x27, 0x10, 0x00, 0x50, 0x00, 0x00, //
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x02, //
            0x20, 0x00, 0xc5, 0x18, 0x00, 0x00, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, //
        ],
        (),
        TestContextObject::new(17),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_tcp_port80_nomatch() {
    test_interpreter_and_interpreter2_asm!(
        PROG_TCP_PORT_80,
        [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x06, //
            0x07, 0x08, 0x09, 0x0a, 0x08, 0x00, 0x45, 0x00, //
            0x00, 0x56, 0x00, 0x01, 0x00, 0x00, 0x40, 0x06, //
            0xf9, 0x4d, 0xc0, 0xa8, 0x00, 0x01, 0xc0, 0xa8, //
            0x00, 0x02, 0x00, 0x16, 0x27, 0x10, 0x00, 0x00, //
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x51, 0x02, //
            0x20, 0x00, 0xc5, 0x18, 0x00, 0x00, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, //
        ],
        (),
        TestContextObject::new(18),
        ProgramResult::Ok(0x0),
    );
}

#[test]
fn test_tcp_port80_nomatch_ethertype() {
    test_interpreter_and_interpreter2_asm!(
        PROG_TCP_PORT_80,
        [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x06, //
            0x07, 0x08, 0x09, 0x0a, 0x08, 0x01, 0x45, 0x00, //
            0x00, 0x56, 0x00, 0x01, 0x00, 0x00, 0x40, 0x06, //
            0xf9, 0x4d, 0xc0, 0xa8, 0x00, 0x01, 0xc0, 0xa8, //
            0x00, 0x02, 0x27, 0x10, 0x00, 0x50, 0x00, 0x00, //
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x02, //
            0x20, 0x00, 0xc5, 0x18, 0x00, 0x00, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, //
        ],
        (),
        TestContextObject::new(7),
        ProgramResult::Ok(0x0),
    );
}

#[test]
fn test_tcp_port80_nomatch_proto() {
    test_interpreter_and_interpreter2_asm!(
        PROG_TCP_PORT_80,
        [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x00, 0x06, //
            0x07, 0x08, 0x09, 0x0a, 0x08, 0x00, 0x45, 0x00, //
            0x00, 0x56, 0x00, 0x01, 0x00, 0x00, 0x40, 0x11, //
            0xf9, 0x4d, 0xc0, 0xa8, 0x00, 0x01, 0xc0, 0xa8, //
            0x00, 0x02, 0x27, 0x10, 0x00, 0x50, 0x00, 0x00, //
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x02, //
            0x20, 0x00, 0xc5, 0x18, 0x00, 0x00, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, //
            0x44, 0x44, 0x44, 0x44, //
        ],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0x0),
    );
}

#[test]
fn test_tcp_sack_match() {
    test_interpreter_and_interpreter2_asm!(
        TCP_SACK_ASM,
        TCP_SACK_MATCH,
        (),
        TestContextObject::new(79),
        ProgramResult::Ok(0x1),
    );
}

#[test]
fn test_tcp_sack_nomatch() {
    test_interpreter_and_interpreter2_asm!(
        TCP_SACK_ASM,
        TCP_SACK_NOMATCH,
        (),
        TestContextObject::new(55),
        ProgramResult::Ok(0x0),
    );
}


#[cfg(all(feature = "jit", not(target_os = "windows"), target_arch = "x86_64"))]
fn execute_generated_program(prog: &[u8]) -> bool {
    let max_instruction_count = 1024;
    let mem_size = 1024 * 1024;
    let executable = Executable::<TestContextObject>::from_text_bytes(
        prog,
        Arc::new(BuiltinProgram::new_loader(
            Config {
                enable_instruction_tracing: true,
                ..Config::default()
            },
            FunctionRegistry::default(),
        )),
        SBPFVersion::V2,
        FunctionRegistry::default(),
    );
    let mut executable = if let Ok(executable) = executable {
        executable
    } else {
        return false;
    };
    if executable.verify::<RequisiteVerifier>().is_err() || executable.jit_compile().is_err() {
        return false;
    }
    let (instruction_count_interpreter, tracer_interpreter, result_interpreter) = {
        let mut mem = vec![0u8; mem_size];
        let mut context_object = TestContextObject::new(max_instruction_count);
        let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
        create_vm!(
            vm,
            &executable,
            &mut context_object,
            stack,
            heap,
            vec![mem_region],
            None
        );
        let (instruction_count_interpreter, result_interpreter) =
            vm.execute_program(&executable, true);
        let tracer_interpreter = vm.context_object_pointer.clone();
        (
            instruction_count_interpreter,
            tracer_interpreter,
            result_interpreter,
        )
    };
    let mut mem = vec![0u8; mem_size];
    let mut context_object = TestContextObject::new(max_instruction_count);
    let mem_region = MemoryRegion::new_writable(&mut mem, ebpf::MM_INPUT_START);
    create_vm!(
        vm,
        &executable,
        &mut context_object,
        stack,
        heap,
        vec![mem_region],
        None
    );
    let (instruction_count_jit, result_jit) = vm.execute_program(&executable, false);
    let tracer_jit = &vm.context_object_pointer;
    if format!("{result_interpreter:?}") != format!("{result_jit:?}")
        || !TestContextObject::compare_trace_log(&tracer_interpreter, tracer_jit)
    {
        let analysis =
            solana_rbpf::static_analysis::Analysis::from_executable(&executable).unwrap();
        println!("result_interpreter={result_interpreter:?}");
        println!("result_jit={result_jit:?}");
        let stdout = std::io::stdout();
        analysis
            .disassemble_trace_log(&mut stdout.lock(), &tracer_interpreter.trace_log)
            .unwrap();
        analysis
            .disassemble_trace_log(&mut stdout.lock(), &tracer_jit.trace_log)
            .unwrap();
        panic!();
    }
    if executable.get_config().enable_instruction_meter {
        assert_eq!(instruction_count_interpreter, instruction_count_jit);
    }
    true
}

#[cfg(all(not(windows), target_arch = "x86_64"))]


// SBPFv1 only [DEPRECATED]

#[test]
fn test_err_fixed_stack_out_of_bound() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        max_call_depth: 3,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        stb [r10-0x4000], 0
        exit",
        config,
        [],
        (),
        TestContextObject::new(1),
        ProgramResult::Err(EbpfError::AccessViolation(
            AccessType::Store,
            0x1FFFFD000,
            1,
            "program"
        )),
    );
}

#[test]
fn test_lddw() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        lddw r0, 0x1122334455667788
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x1122334455667788),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        lddw r0, 0x0000000080000000
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Ok(0x80000000),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        mov r1, 0
        mov r2, 0
        lddw r0, 0x1
        ja +2
        lddw r1, 0x1
        lddw r2, 0x1
        add r1, r2
        add r0, r1
        exit
        ",
        config.clone(),
        [],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0x2),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r8, 0x1
        lsh64 r8, 0x20
        or64 r8, 0x28
        callx r8
        lddw r0, 0x1122334455667788
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r8, 0x1
        lsh64 r8, 0x20
        or64 r8, 0x28
        callx r8
        lddw r0, 0x1122334455667788
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Err(EbpfError::UnsupportedInstruction),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r1, 0x1
        lsh64 r1, 0x20
        or64 r1, 0x38
        callx r1
        mov r0, r0
        mov r0, r0
        lddw r0, 0x1122334455667788
        exit
        ",
        config.clone(),
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Err(EbpfError::UnsupportedInstruction),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        lddw r1, 0x100000038
        callx r1
        mov r0, r0
        mov r0, r0
        exit
        lddw r0, 0x1122334455667788
        exit
        ",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Err(EbpfError::UnsupportedInstruction),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0
        lddw r1, 0x1
        mov r2, 0
        exit
        ",
        config,
        [],
        (),
        TestContextObject::new(2),
        ProgramResult::Err(EbpfError::ExceededMaxInstructions),
    );
}

#[test]
fn test_le() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        ldxh r0, [r1]
        le16 r0
        exit",
        config.clone(),
        [0x22, 0x11],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1122),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1]
        le16 r0
        exit",
        config.clone(),
        [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x2211),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        ldxw r0, [r1]
        le32 r0
        exit",
        config.clone(),
        [0x44, 0x33, 0x22, 0x11],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x11223344),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1]
        le32 r0
        exit",
        config.clone(),
        [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x44332211),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        ldxdw r0, [r1]
        le64 r0
        exit",
        config,
        [0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x1122334455667788),
    );
}

#[test]
fn test_neg() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 2
        neg32 r0
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0xfffffffe),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 2
        neg r0
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0xfffffffffffffffe),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 3
        sub32 r0, 1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(2),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 3
        sub r0, 1
        exit",
        config,
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(2),
    );
}

#[test]
fn test_callx_imm() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        mov64 r0, 0x0
        mov64 r8, 0x1
        lsh64 r8, 0x20
        or64 r8, 0x30
        callx r8
        exit
        function_foo:
        mov64 r0, 0x2A
        exit",
        config,
        [],
        (),
        TestContextObject::new(8),
        ProgramResult::Ok(42),
    );
}

#[test]
fn test_mul() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 3
        mul32 r0, 4
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0xc),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 3
        mov r1, 4
        mul32 r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0xc),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0x40000001
        mov r1, 4
        mul32 r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x4),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0x40000001
        mul r0, 4
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x100000004),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0x40000001
        mov r1, 4
        mul r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x100000004),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, -1
        mul32 r0, 4
        exit",
        config,
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0xFFFFFFFFFFFFFFFC),
    );
}

#[test]
fn test_div() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 12
        lddw r1, 0x100000004
        div32 r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x3),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        lddw r0, 0x10000000c
        div32 r0, 4
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x3),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        lddw r0, 0x10000000c
        mov r1, 4
        div32 r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x3),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0xc
        lsh r0, 32
        div r0, 4
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(4),
        ProgramResult::Ok(0x300000000),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov r0, 0xc
        lsh r0, 32
        mov r1, 4
        div r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Ok(0x300000000),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 1
        mov32 r1, 0
        div r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Err(EbpfError::DivideByZero),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 1
        mov32 r1, 0
        div32 r0, r1
        exit",
        config,
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Err(EbpfError::DivideByZero),
    );
}

#[test]
fn test_mod() {
    let config = Config {
        enabled_sbpf_versions: SBPFVersion::V1..=SBPFVersion::V1,
        ..Config::default()
    };
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 5748
        mod32 r0, 92
        mov32 r1, 13
        mod32 r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(5),
        ProgramResult::Ok(0x5),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        lddw r0, 0x100000003
        mod32 r0, 3
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Ok(0x0),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, -1316649930
        lsh r0, 32
        or r0, 0x100dc5c8
        mov32 r1, 0xdde263e
        lsh r1, 32
        or r1, 0x3cbef7f3
        mod r0, r1
        mod r0, 0x658f1778
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(9),
        ProgramResult::Ok(0x30ba5a04),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 1
        mov32 r1, 0
        mod r0, r1
        exit",
        config.clone(),
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Err(EbpfError::DivideByZero),
    );
    test_interpreter_and_interpreter2_asm!(
        "
        mov32 r0, 1
        mov32 r1, 0
        mod32 r0, r1
        exit",
        config,
        [],
        (),
        TestContextObject::new(3),
        ProgramResult::Err(EbpfError::DivideByZero),
    );
}
