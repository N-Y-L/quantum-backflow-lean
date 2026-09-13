# Proof verification

`check_proofs.py` scans Lean source and invokes `Axioms.lean`. The latter audits all
project declarations by originating module, including private helpers, and traverses
both statement and proof dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The source scan is supplementary.

`test_check_proofs.py` exercises the scanner and import coverage. `results.json` records
verification commands and source hashes after successful checks. Dependency caches
and build products are excluded from the repository.
