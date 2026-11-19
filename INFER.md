How to use the infer option:

Call VerCors with `--infer`.

Options:

- `--infer-out <path>` specifies output path
- `--infer-tri <path>` can be used to specify a path for TriCera
- `--infer-loops` specifies that loop invariants should also be generated
- `--infer-globals` is needed if you want TriCera to nondeterministically evaluate globals
- `--infer-verbose` prints the result of the contract inference to the terminal