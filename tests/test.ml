open Interp_test

type test_case = {
  dis : string; 
  lp_std : int64 list;
  lm_std : int64 list;
  lc_std : int64 list;
  v : int64;
  fuel : int64;
  result_expected : int64;
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)

let run_test_case test_case =
  let v = Interp_test.int_of_standard_int test_case.v in
  let fuel = Interp_test.nat_of_int test_case.fuel in
  let res = Interp_test.int_of_standard_int test_case.result_expected in
  let lp = Interp_test.int_list_of_standard_int_list test_case.lp_std in
  let lm = Interp_test.int_list_of_standard_int_list test_case.lm_std in
  let lc = Interp_test.int_list_of_standard_int_list test_case.lc_std in
  let result = Interp_test.bpf_interp_test lp lm lc v fuel res in
  let color = if result then green else red in
  Printf.printf "%s%-25s result: %s%b%s\n" color test_case.dis color result reset

let test_cases = [
  (*
    mov32 r1, 1
    mov32 r0, r1
    exit*)
  {
    dis = "test_mov";
    lp_std = [180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 188L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 3L;
    result_expected = 0x01L;
  };
  (*
    mov32 r0, -1
    exit*)
  {
    dis = "test_mov32_imm_large";
    lp_std = [180L; 0L; 0L; 0L; 255L; 255L; 255L; 255L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 2L;
    result_expected = 0xffffffffL;
  };
  (*
    mov32 r1, -1
    mov32 r0, r1
    exit*)
  {
    dis = "test_mov_large";
    lp_std = [180L; 1L; 0L; 0L; 255L; 255L; 255L; 255L; 188L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 3L;
    result_expected = 0xffffffffL;
  };
  (*
    mov r0, 1
    mov r6, r0
    mov r7, r6
    mov r8, r7
    mov r9, r8
    mov r0, r9
    exit*)
  {
    dis = "test_bounce";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 191L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 103L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 120L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 137L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 7L;
    result_expected = 0x01L;
  };
  (*
    mov32 r0, 0L
    mov32 r1, 2
    add32 r0, 1
    add32 r0, r1
    exit*)
    {
      dis = "test_add32";
      lp_std = [180L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 2L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 12L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
      lm_std = [];
      lc_std = [];
      v = 2L;
      fuel = 5L;
      result_expected = 0x3L;
    };
  (*
    mov32 r0, 0L
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
    exit*)
    {
      dis = "test_alu32_arithmetic";
      lp_std = [180L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 180L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 180L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 180L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 180L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 180L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 180L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 180L; 9L; 0L; 0L; 9L; 0L; 0L; 0L; 20L; 0L; 0L; 0L; 13L; 0L; 0L; 0L; 28L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 4L; 0L; 0L; 0L; 23L; 0L; 0L; 0L; 12L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 134L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 142L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 70L; 0L; 0L; 0L; 2L; 0L; 0L; 0L; 78L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
      lm_std = [];
      lc_std = [];
      v = 2L;
      fuel = 19L;
      result_expected = 110L;
    };  
  (*
    mov r0, 0L
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
    exit*)
    {
      dis = "test_alu64_arithmetic";
      lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 183L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 183L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 183L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 183L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 183L; 9L; 0L; 0L; 9L; 0L; 0L; 0L; 23L; 0L; 0L; 0L; 13L; 0L; 0L; 0L; 31L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 23L; 0L; 0L; 0L; 15L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 150L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 158L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 86L; 0L; 0L; 0L; 2L; 0L; 0L; 0L; 94L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
      lm_std = [];
      lc_std = [];
      v = 2L;
      fuel = 19L;
      result_expected = 110L;
    };  
  (*
    mov r0, r1
    mov r2, 30
    mov r3, 0L
    mov r4, 20
    mov r5, 0L
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
    exit*)
  {
    dis = "test_lmul128";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 30L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 4L; 0L; 0L; 20L; 0L; 0L; 0L; 183L; 5L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 67L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 37L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 53L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 191L; 67L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 3L; 0L; 0L; 32L; 0L; 0L; 0L; 191L; 54L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 15L; 101L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 191L; 70L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 158L; 36L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 6L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 6L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 101L; 0L; 0L; 0L; 0L; 0L; 0L; 158L; 35L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 191L; 2L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 15L; 37L; 0L; 0L; 0L; 0L; 0L; 0L; 123L; 81L; 8L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 123L; 1L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L]; 
    lm_std = [0L; 16L];
    lc_std = [];
    v = 2L;
    fuel = 42L;
    result_expected = 600L;
  };
(*
    mov32 r0, 0L
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
    exit*)
  {
    dis = "test_alu32_logic";
    lp_std = [180L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 180L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 180L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 180L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 180L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 180L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 180L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 180L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 76L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 68L; 0L; 0L; 0L; 160L; 0L; 0L; 0L; 84L; 0L; 0L; 0L; 163L; 0L; 0L; 0L; 180L; 9L; 0L; 0L; 145L; 0L; 0L; 0L; 92L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 100L; 0L; 0L; 0L; 22L; 0L; 0L; 0L; 108L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 116L; 0L; 0L; 0L; 19L; 0L; 0L; 0L; 124L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 164L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 172L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L]; 
    lm_std = [0L; 16L];
    lc_std = [];
    v = 2L;
    fuel = 21L;
    result_expected = 0x11L;
  };
(*
    mov r0, 0L
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
    exit*)
  {
    dis = "test_alu64_logic";
    lp_std = [183L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 183L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 183L; 2L; 0L; 0L; 2L; 0L; 0L; 0L; 183L; 3L; 0L; 0L; 3L; 0L; 0L; 0L; 183L; 4L; 0L; 0L; 4L; 0L; 0L; 0L; 183L; 5L; 0L; 0L; 5L; 0L; 0L; 0L; 183L; 6L; 0L; 0L; 6L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 7L; 0L; 0L; 0L; 183L; 8L; 0L; 0L; 8L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 71L; 0L; 0L; 0L; 160L; 0L; 0L; 0L; 87L; 0L; 0L; 0L; 163L; 0L; 0L; 0L; 183L; 9L; 0L; 0L; 145L; 0L; 0L; 0L; 95L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 22L; 0L; 0L; 0L; 111L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 119L; 0L; 0L; 0L; 19L; 0L; 0L; 0L; 127L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 167L; 0L; 0L; 0L; 3L; 0L; 0L; 0L; 175L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L]; 
    lm_std = [0L; 16L];
    lc_std = [];
    v = 2L;
    fuel = 23L;
    result_expected = 0x11L;
  };
  (*
    mov r0, 8
    mov32 r1, 0x00000001
    hor64 r1, 0x00000001
    arsh32 r0, r1
    exit*)
  {
    dis = "test_arsh32_high_shift";
    lp_std = [183L; 0L; 0L; 0L; 8L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 247L; 1L; 0L; 0L; 1L; 0L; 0L; 0L; 204L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 5L;
    result_expected = 0x4L;   
  };
  (*
    mov32 r0, 0xf8
    lsh32 r0, 28
    arsh32 r0, 16
    exit*)
  {
    dis = "test_arsh32_imm";
    lp_std = [180L; 0L; 0L; 0L; 248L; 0L; 0L; 0L; 100L; 0L; 0L; 0L; 28L; 0L; 0L; 0L; 196L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 4L;
    result_expected = 0xffff8000L;   
  };
  (*
    mov32 r0, 0xf8
    mov32 r1, 16
    lsh32 r0, 28
    arsh32 r0, r1
    exit*)
  {
    dis = "test_arsh32_reg";
    lp_std = [180L; 0L; 0L; 0L; 248L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 16L; 0L; 0L; 0L; 100L; 0L; 0L; 0L; 28L; 0L; 0L; 0L; 204L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 5L;
    result_expected = 0xffff8000L;   
  };
  (*
    mov32 r0, 1
    lsh r0, 63
    arsh r0, 55
    mov32 r1, 5
    arsh r0, r1
    exit*)
  {
    dis = "test_arsh64";
    lp_std = [180L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 63L; 0L; 0L; 0L; 199L; 0L; 0L; 0L; 55L; 0L; 0L; 0L; 180L; 1L; 0L; 0L; 5L; 0L; 0L; 0L; 207L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 6L;
    result_expected = 0xfffffffffffffff8L;    
  };
  (*
    mov r0, 0x1
    mov r7, 4
    lsh r0, r7
    exit*)
  {
    dis = "test_lsh64_reg";
    lp_std = [183L; 0L; 0L; 0L; 1L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 4L; 0L; 0L; 0L; 111L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 64L;
    result_expected = 0x10L;   
  };
  (*
    xor r0, r0
    add r0, -1
    rsh32 r0, 8
    exit*)
  {
    dis = "test_rhs32_imm";
    lp_std = [175L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 7L; 0L; 0L; 0L; 255L; 255L; 255L; 255L; 116L; 0L; 0L; 0L; 8L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 4L;
    result_expected = 0x00ffffffL;   
  };
  (*
    mov r0, 0x10
    mov r7, 4
    rsh r0, r7
    exit*)
  {
    dis = "test_rsh64_reg";
    lp_std = [183L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 183L; 7L; 0L; 0L; 4L; 0L; 0L; 0L; 127L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 4L;
    result_expected = 0x1L;   
  };
  (*
    ldxh r0, [r1]
    be16 r0
    exit*)
  {
    dis = "test_be16";
    lp_std = [105L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L];
    lc_std = [];
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122L;   
  };
  (*
    ldxdw r0, [r1]
    be16 r0
    exit*)
  {
    dis = "test_be16_high";
    lp_std = [121L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122L;   
  };
  (*
    ldxw r0, [r1]
    be32 r0
    exit*)
  {
    dis = "test_be32";
    lp_std = [97L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L];
    lc_std = [];
    v = 1L;
    fuel = 3L;
    result_expected = 0x11223344L;   
  };
  (*
    ldxdw r0, [r1]
    be32 r0
    exit*)
  {
    dis = "test_be32_high";
    lp_std = [121L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    v = 1L;
    fuel = 3L;
    result_expected = 0x11223344L;   
  };
  (*
    ldxdw r0, [r1]
    be64 r0
    exit*)
  {
    dis = "test_be64";
    lp_std = [121L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 64L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L];
    lc_std = [];
    v = 1L;
    fuel = 3L;
    result_expected = 0x1122334455667788L;   
  };
  (*
    hor64 r0, 0x10203040
    hor64 r0, 0x01020304
    exit*)
  {
    dis = "test_hor64";
    lp_std = [247L; 0L; 0L; 0L; 64L; 48L; 32L; 16L; 247L; 0L; 0L; 0L; 4L; 3L; 2L; 1L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [];
    lc_std = [];
    v = 2L;
    fuel = 3L;
    result_expected = 0x1122334400000000L;   
  };
  (*
    ldxb r0, [r1+2]
    exit*)
  {
    dis = "test_ldxb";
    lp_std = [113L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0xccL; 0xddL];
    lc_std = [];
    v = 2L;
    fuel = 2L;
    result_expected = 0x11L;   
  };
  (*
    ldxh r0, [r1+2]
    exit*)
  {
    dis = "test_ldxh";
    lp_std = [105L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0xccL; 0xddL];
    lc_std = [];
    v = 2L;
    fuel = 2L;
    result_expected = 0x2211L;   
  };
  (*
    ldxw r0, [r1+2]
    exit*)
  {
    dis = "test_ldxw";
    lp_std = [97L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0x33L; 0x44L; 0xccL; 0xddL];
    lc_std = [];
    v = 2L;
    fuel = 2L;
    result_expected = 0x44332211L;   
  };
  (*
    mov r0, r1
    sth [r0], 0x1234
    ldxh r0, [r0]
    exit*)
  {
    dis = "test_ldxh_same_reg";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 106L; 0L; 0L; 0L; 52L; 18L; 0L; 0L; 105L; 0L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xffL; 0xffL];
    lc_std = [];
    v = 2L;
    fuel = 4L;
    result_expected = 0x1234L;   
  };
  (* //Fatal error: exception Stack_overflow
    ldxdw r0, [r1+2]
    exit*)
  {
    dis = "test_lldxdw";
    lp_std = [121L; 16L; 2L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0xaaL; 0xbbL; 0x11L; 0x22L; 0x33L; 0x44L; 0x55L; 0x66L; 0x77L; 0x88L; 0xccL; 0xddL];
    lc_std = [];
    v = 2L;
    fuel = 2L;
    result_expected = 0x8877665544332211L;   
  };
  (*
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
    exit*)
  {
    dis = "test_ldxb_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 103L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 113L; 8L; 1L; 0L; 0L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 4L; 0L; 0L; 0L; 113L; 7L; 2L; 0L; 0L; 0L; 0L; 0L; 103L; 7L; 0L; 0L; 8L; 0L; 0L; 0L; 113L; 6L; 3L; 0L; 0L; 0L; 0L; 0L; 103L; 6L; 0L; 0L; 12L; 0L; 0L; 0L; 113L; 5L; 4L; 0L; 0L; 0L; 0L; 0L; 103L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 113L; 4L; 5L; 0L; 0L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 20L; 0L; 0L; 0L; 113L; 3L; 6L; 0L; 0L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 24L; 0L; 0L; 0L; 113L; 2L; 7L; 0L; 0L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 28L; 0L; 0L; 0L; 113L; 1L; 8L; 0L; 0L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 113L; 0L; 9L; 0L; 0L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 36L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x01L; 0x02L; 0x03L; 0x04L; 0x05L; 0x06L; 0x07L; 0x08L; 0x09L];
    lc_std = [];
    v = 2L;
    fuel = 31L;
    result_expected = 0x9876543210L;   
  };
  (*
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
    exit*)
  {
    dis = "test_ldxh_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 9L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 8L; 2L; 0L; 0L; 0L; 0L; 0L; 220L; 8L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 8L; 0L; 0L; 4L; 0L; 0L; 0L; 105L; 7L; 4L; 0L; 0L; 0L; 0L; 0L; 220L; 7L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 7L; 0L; 0L; 8L; 0L; 0L; 0L; 105L; 6L; 6L; 0L; 0L; 0L; 0L; 0L; 220L; 6L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 6L; 0L; 0L; 12L; 0L; 0L; 0L; 105L; 5L; 8L; 0L; 0L; 0L; 0L; 0L; 220L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 4L; 10L; 0L; 0L; 0L; 0L; 0L; 220L; 4L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 4L; 0L; 0L; 20L; 0L; 0L; 0L; 105L; 3L; 12L; 0L; 0L; 0L; 0L; 0L; 220L; 3L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 3L; 0L; 0L; 24L; 0L; 0L; 0L; 105L; 2L; 14L; 0L; 0L; 0L; 0L; 0L; 220L; 2L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 2L; 0L; 0L; 28L; 0L; 0L; 0L; 105L; 1L; 16L; 0L; 0L; 0L; 0L; 0L; 220L; 1L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 105L; 0L; 18L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 103L; 0L; 0L; 0L; 36L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x02L; 0x00L; 0x03L; 0x00L; 0x04L; 0x00L; 0x05L; 0x00L; 0x06L; 0x00L; 0x07L; 0x00L; 0x08L; 0x00L; 0x09L];
    lc_std = [];
    v = 1L;
    fuel = 41L;
    result_expected = 0x9876543210L;   
  };
  (*
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
    exit*)
  {
    dis = "test_ldxh_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 105L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 9L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 8L; 2L; 0L; 0L; 0L; 0L; 0L; 220L; 8L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 7L; 4L; 0L; 0L; 0L; 0L; 0L; 220L; 7L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 6L; 6L; 0L; 0L; 0L; 0L; 0L; 220L; 6L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 5L; 8L; 0L; 0L; 0L; 0L; 0L; 220L; 5L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 4L; 10L; 0L; 0L; 0L; 0L; 0L; 220L; 4L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 3L; 12L; 0L; 0L; 0L; 0L; 0L; 220L; 3L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 2L; 14L; 0L; 0L; 0L; 0L; 0L; 220L; 2L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 1L; 16L; 0L; 0L; 0L; 0L; 0L; 220L; 1L; 0L; 0L; 16L; 0L; 0L; 0L; 105L; 0L; 18L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 16L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std = [0x00L; 0x01L; 0x00L; 0x02L; 0x00L; 0x04L; 0x00L; 0x08L; 0x00L; 0x10L; 0x00L; 0x20L; 0x00L; 0x40L; 0x00L; 0x80L; 0x01L; 0x00L; 0x02L; 0x00L];
    lc_std = [];
    v = 1L;
    fuel = 31L;
    result_expected = 0x3ffL;   
  };
  (*
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
    exit*)
  {
    dis = "test_ldxw_all";
    lp_std = [191L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 97L; 9L; 0L; 0L; 0L; 0L; 0L; 0L; 220L; 9L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 8L; 4L; 0L; 0L; 0L; 0L; 0L; 220L; 8L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 7L; 8L; 0L; 0L; 0L; 0L; 0L; 220L; 7L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 6L; 12L; 0L; 0L; 0L; 0L; 0L; 220L; 6L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 5L; 16L; 0L; 0L; 0L; 0L; 0L; 220L; 5L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 4L; 20L; 0L; 0L; 0L; 0L; 0L; 220L; 4L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 3L; 24L; 0L; 0L; 0L; 0L; 0L; 220L; 3L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 2L; 28L; 0L; 0L; 0L; 0L; 0L; 220L; 2L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 1L; 32L; 0L; 0L; 0L; 0L; 0L; 220L; 1L; 0L; 0L; 32L; 0L; 0L; 0L; 97L; 0L; 36L; 0L; 0L; 0L; 0L; 0L; 220L; 0L; 0L; 0L; 32L; 0L; 0L; 0L; 79L; 16L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 32L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 48L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 64L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 80L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 96L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 112L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 128L; 0L; 0L; 0L; 0L; 0L; 0L; 79L; 144L; 0L; 0L; 0L; 0L; 0L; 0L; 149L; 0L; 0L; 0L; 0L; 0L; 0L; 0L];
    lm_std =[
      0x00L; 0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x02L;
      0x00L; 0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0x08L;
      0x00L; 0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L;
      0x00L; 0x00L; 0x04L; 0x00L; 0x00L; 0x00L; 0x08L; 0x00L;
      0x00L; 0x01L; 0x00L; 0x00L; 0x00L; 0x02L; 0x00L; 0x00L];
    lc_std = [];
    v = 1L;
    fuel = 31L;
    result_expected = 0x030f0fL;   
  };
]

let () =
  List.iter run_test_case test_cases
