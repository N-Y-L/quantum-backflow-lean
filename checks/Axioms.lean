import QuantumBackflow
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Audit the trusted dependencies of the public results

Run `lake build` before `lake env lean checks/Axioms.lean`.

The project audit selects declarations by their originating module, including private
declarations and declarations outside the `QuantumBackflow` namespace. It traverses their
types and proofs recursively, including imported dependencies, and rejects unsafe
project declarations. The named checks below also print the public results' dependencies.
The audit fails if any closure contains anything beyond Lean's standard propositional
extensionality, classical choice, and quotient soundness principles.
The accompanying source scan is supplementary; this dependency check is authoritative.
-/

open Lean Elab Command

/-- Audit all declarations originating in the project library, regardless of namespace. -/
elab "audit_project_axioms" : command => do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun declarations name info =>
    match env.getModuleIdxFor? name with
    | some index =>
        if (`QuantumBackflow).isPrefixOf env.header.moduleNames[index.toNat]! then
          declarations.push (name, info)
        else declarations
    | none => declarations
  if declarations.isEmpty then
    throwError "No declarations from the QuantumBackflow project modules were found"
  for (name, info) in declarations do
    if info.isUnsafe then
      throwError "Unsafe project declaration: {name}"
  -- Sharing the visited set avoids retraversing mathlib for every declaration.
  let collect : Lean.CollectAxioms.M Unit :=
    declarations.forM fun (name, _) => Lean.CollectAxioms.collect name
  let (_, state) := (collect.run env).run {}
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := state.axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Untrusted dependencies in project declarations: {unexpected.toList}"
  logInfo m!"Audited all {declarations.size} declarations from the QuantumBackflow project modules"

/-- Check the transitive dependency closure, then print it using Lean's standard command. -/
elab "audit_axioms " decl:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let actual ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := actual.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Untrusted dependencies in {name}: {unexpected.toList}"
  elabCommand (← `(#print axioms $decl))

audit_project_axioms

audit_axioms QuantumBackflow.twoBand_backflow
audit_axioms QuantumBackflow.explicit_quantum_backflow
audit_axioms QuantumBackflow.quantum_backflow_physical
audit_axioms QuantumBackflow.shifted_twoBand_backflow
audit_axioms QuantumBackflow.quantum_backflow_exists
audit_axioms QuantumBackflow.arbitraryBands_backflow
audit_axioms QuantumBackflow.shifted_arbitraryBands_backflow
audit_axioms QuantumBackflow.quantum_backflow_with_probability_above_cutoff
