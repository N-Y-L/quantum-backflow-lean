# Contributing

State assumptions, quantifiers, and physical conventions explicitly. Use compact prose,
standard notation, descriptive filenames, and GitHub-rendered mathematics. Keep the
README and proof guide consistent with the checked statements. Preserve attribution.

Every proof must compile with the pinned toolchain and pass the dependency audit.
Do not add unfinished proofs, new axioms, unsafe declarations, or native decision procedures.
Analytic hypotheses must not assume the claimed transport identity or probability gain.
Add every library module to `QuantumBackflow.lean` so the audit covers it.

Before recording verification, run:

```sh
lake build --wfail
python3 -m unittest discover -s checks -p 'test_*.py'
python3 checks/check_proofs.py
lake env leanchecker QuantumBackflow
```

Use `main` for checked work. Publication is reserved for the owner in GitHub Desktop.
