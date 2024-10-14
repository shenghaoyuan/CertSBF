# Validation Framework

## Folder Structure

- **`./rbpf`**: Contains the original Solana eBPF VM and custom  mechanism for program (`interpreter_test`) and instruction-level (`step_test`) testing.
- **`./data`**: Stores all benchmarks and test data.
-  **`./exec-semantics`**: holds the OCaml code extracted from Isabelle/HOL and associated glue code.