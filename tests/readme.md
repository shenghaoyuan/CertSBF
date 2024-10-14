

## Folder Structure

- **`./rbpf`**: Contains the original Solana eBPF VM and custom  mechanism for program (`interpreter_test`) and instruction-level (`step_test`) testing.
- **`./data`**: Stores all benchmarks and test data.

-  **`./exec-semantics`**: holds the OCaml code extracted from Isabelle proofs and associated glue code.


## Make Commands

- **`make generator`**: Generate random instruction test cases.
  - Use `make generator num=X` to specify the number of cases.
- **`make micro-test`**: Compiles and runs instruction-level tests using the generated cases.
- **`make macro-test`**: Compiles and runs program-level tests using the Solana official test suite in `./rbpf/tests/execution.rs`.
- **`make clean`**: Removes all build artifacts.