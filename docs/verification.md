# Verification

Local checks recorded on 13 September 2026 with Lean 4.28.0 and mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

| Check | Result |
| --- | --- |
| Build with warnings treated as errors | Passed |
| Fresh source copy, with no project build artifacts | Passed |
| Source scan: 14 Lean files | Passed |
| Transitive audit: all 267 project declarations | Passed |
| Compiled-proof recheck with `leanchecker QuantumBackflow` | Passed |
| Verification-tool regression tests | 8 passed |
| Mathematical review and documentation links | No defects found |

The fresh build reused the pinned mathlib dependency cache. Its mathlib checkout was
clean and matched the manifest. Every proof source in the delivered repository matches
the independently rebuilt and rechecked copy.

The audit selects declarations by originating module, including private declarations
and helpers outside the public namespace. It permits only `propext`, `Classical.choice`,
and `Quot.sound`. No unfinished proofs, added axioms, unsafe project declarations, or
native decision procedures were found. These checks validate the stated Lean results;
the [proof guide](proof-guide.md) explains their assumptions and conclusions.

[`checks/results.json`](../checks/results.json) records commands, exit codes, and source
hashes. Regenerate the record after source changes. Hosted workflow results are separate
from this local record.
