# Quantum backflow in Lean

A Lean 4 formalization of a free particle with strictly positive momentum with probability one and an increasing probability of lying to the left of a boundary. The construction uses square-integrable continuum wave packets with compact spectral support.

The construction works for any two separated strictly positive spectral bands, with a suitable explicit coefficient, and any positive free-evolution coefficient. It gives an open interval on which the normalized left probability has positive derivative and is strictly increasing, and can be placed at any prescribed time and spatial boundary.

## Mathematical statement

Let `0 < a < b < d < e`, and set

\[
\phi(k)=\mathbf 1_{[a,b]}(k)-r\mathbf 1_{[d,e]}(k),\qquad
\psi(t,x)=\int_{\mathbb R}e^{i(kx-ck^2t)}\phi(k)\,dk,
\quad c>0.
\]

Assume the real spectral moments satisfy

\[
A=(b-a)-r(e-d)>0,\qquad
B=\frac{b^2-a^2}{2}-r\frac{e^2-d^2}{2}<0.
\]

Then `twoBand_backflow` proves:

- The evolved spectrum has finite positive squared norm and positive momentum probability exactly one at every time.
- The position wave has finite positive squared norm, conserved under the stated free evolution.
- The wave satisfies the free Schrödinger equation.
- The normalized left probability lies in `[0,1]` at every time and, throughout some open interval around zero, has positive derivative and is strictly increasing.

The statement and bundled conclusions are in [`MainTheorem.lean`](QuantumBackflow/MainTheorem.lean). No negative-current or probability-increase hypothesis is assumed in this two-band theorem: both are derived from the spectral moment inequalities.

For the explicit choice `φ = 1_[1,2] − (1/2) 1_[3,4]`, the spectral squared norm is `5/4`, `A = 1/2`, `B = −1/4`, and the unnormalized boundary current is `−c/4`. The theorem `explicit_quantum_backflow` instantiates this example. The equivalent profile `exampleProfile = 2φ` has raw current `−c`; multiplying a wave by a nonzero constant does not change its Born probabilities.

For **every** pair of separated positive bands, a coefficient exists without additional moment assumptions:

\[
r=\frac{(b-a)(a+b+d+e)}{2(e-d)(d+e)}.
\]

[`arbitraryBands_backflow`](QuantumBackflow/ArbitraryBands.lean) verifies this choice. Its translated version places backflow at any prescribed time and boundary. [`quantum_backflow_with_probability_above_cutoff`](QuantumBackflow/Generalizations.lean) further proves that the whole spectrum can lie above any prescribed finite cutoff, with probability one throughout evolution. No fixed lower bound on the amount of backflow is asserted.

## Conventions and verification scope

The integration variable `k` is wave number (named `p` in some Lean definitions). Physical momentum is `ℏ k`. For positive `ℏ` and mass `m`, choose `c = ℏ/(2m)`; then

\[
\partial_t\psi=ci\,\partial_x^2\psi,\qquad
j=2c\operatorname{Im}(\overline\psi\,\partial_x\psi).
\]

The inverse Fourier integral omits a normalization prefactor. Born probabilities are ratios of squared-norm integrals, for both the spectral and position representations. The position normalizer is finite, positive, and constant in time. The normalized current is `j / totalMass`.

The formalization uses an explicit Fourier pair and normalized density integrals. Position mass conservation follows from the continuity equation and decay. Plancherel's norm identity and the abstract spectral-measure construction of the momentum observable are outside its scope.

These existence results do not determine the optimal Bracken–Melloy constant or prove the more recent arbitrary-momentum or repeated-interval generalizations.

## Reproduce the checks

The toolchain and mathlib revision are pinned in [`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml).

```sh
lake exe cache get
lake build --wfail
python3 -m unittest discover -s checks -p 'test_*.py'
python3 checks/check_proofs.py
lake env leanchecker QuantumBackflow
```

The integrity checks reject unfinished proofs and added axioms, and audit transitive axiom dependencies of project declarations. Standard Lean foundations such as classical choice and propositional extensionality remain part of the trusted basis; “no added axioms” is not a claim of constructive mathematics. The GitHub workflow also configures independent proof rechecking with `leanchecker`.

## Reading and attribution

Start with the [proof guide](docs/proof-guide.md), then the [source and scope notes](docs/README.md). The [prior-art check](docs/prior-art.md) documents the public searches conducted on 13 September 2026. No prior proof-assistant formalization was identified in those searches; this is not a claim of priority.

Quantum backflow itself is established physics. See the [Yearsley–Halliwell introduction](https://arxiv.org/abs/1301.4893), its references to Allcock and Bracken–Melloy, and the repository [bibliography](references.bib).
