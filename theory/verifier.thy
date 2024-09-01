section \<open> Verifier of Solana rBPF \<close>

theory verifier
imports
  Main
  rBPFCommType rBPFSyntax
  ebpf rustCommType
begin

datatype VerifierError =
    ProgramLengthNotMultiple
  | NoProgram
  | DivisionByZero usize
  | UnsupportedLEBEArgument usize
  | LDDWCannotBeLast
  | IncompleteLDDW usize
  | InfiniteLoop usize
  | JumpOutOfCode usize usize
  | JumpToMiddleOfLDDW usize usize
  | InvalidSourceRegister usize
  | CannotWriteR10 usize
  | InvalidDestinationRegister usize
  | UnknownOpCode u8 usize
  | ShiftWithOverflow u64 u64 usize
  | InvalidRegister usize
  | InvalidFunction usize

definition check_prog_len :: "u8 list \<Rightarrow> (unit, VerifierError) Result" where
" check_prog_len prog = (
  if (length prog) mod INSN_SIZE \<noteq> 0 then
    Err ProgramLengthNotMultiple
  else if length prog = 0 then
    Err NoProgram
  else
    Ok ()
)"

end