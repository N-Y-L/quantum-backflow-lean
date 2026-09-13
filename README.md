# Quantum backflow in Lean

A Lean 4 formalization of quantum backflow: a free particle has strictly positive momentum with probability one, while its probability of lying to the left of a boundary increases. The construction uses square-integrable wave packets whose spectra are supported on two separated positive bands.

## Mathematical statement

Let $0<a<b<d<e$, and set

$$
\phi(k)=\mathbf 1_{[a,b]}(k)-r\mathbf 1_{[d,e]}(k),\qquad
\psi(t,x)=\int_{\mathbb R}e^{i(kx-ck^2t)}\phi(k)\,dk,
\quad c>0.
$$

Assume the real spectral moments satisfy

$$
A=(b-a)-r(e-d)>0,\qquad
B=\frac{b^2-a^2}{2}-r\frac{e^2-d^2}{2}<0.
$$

Then `twoBand_backflow` proves:

- The evolved spectrum has finite positive squared norm and positive momentum probability exactly one at every time.
- The position wave has finite positive squared norm, conserved under the stated free evolution.
- The wave satisfies the free Schrödinger equation.
- The normalized left probability lies in $[0,1]$ at every time and, throughout some open interval around zero, has positive derivative and is strictly increasing.

The statement is in [`MainTheorem.lean`](QuantumBackflow/MainTheorem.lean). Negative current and probability increase follow from the spectral moment inequalities.

For $\phi=\mathbf{1}_{[1,2]}-\frac{1}{2}\mathbf{1}_{[3,4]}$, the spectral squared norm is $5/4$, $A=1/2$, $B=-1/4$, and the unnormalized boundary current is $-c/4$. The theorem `explicit_quantum_backflow` proves this case.

For every $0<a<b<d<e$, the moment inequalities hold with

$$
r=\frac{(b-a)(a+b+d+e)}{2(e-d)(d+e)}.
$$

[`ArbitraryBands.lean`](QuantumBackflow/ArbitraryBands.lean) verifies this choice and places backflow at any prescribed time and boundary. [`Generalizations.lean`](QuantumBackflow/Generalizations.lean) proves that the spectrum can lie above any finite cutoff with probability one throughout evolution. These are existence results; they give no uniform lower bound on the amount or duration of backflow.

## Conventions

The integration variable $k$ is wave number (named `p` in some Lean definitions). Physical momentum is $\hbar k$. For positive $\hbar$ and mass $m$, choose $c=\hbar/(2m)$; then

$$
\partial_t\psi=ci\,\partial_x^2\psi,\qquad
j=2c\Im(\overline{\psi}\,\partial_x\psi).
$$

Born probabilities are ratios of squared-norm integrals; the normalized current is $j/\int_{\mathbb R}|\psi|^2\,dx$. The [proof guide](docs/proof-guide.md#normalization) explains this convention and the analytic assumptions.

## Reproduce the checks

The toolchain and mathlib revision are pinned in [`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml).

```sh
lake exe cache get
lake build --wfail
python3 -m unittest discover -s checks -p 'test_*.py'
python3 checks/check_proofs.py
lake env leanchecker QuantumBackflow
```

The checks reject unfinished proofs and added axioms, audit transitive dependencies, and recheck compiled proofs with `leanchecker`. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. See the [verification report](docs/verification.md) and [check documentation](checks/README.md).

## Attribution

**Project lead and maintainer:** Neil Yuanting Li.

## Documentation and references

The [proof guide](docs/proof-guide.md) follows the construction through its Lean modules. The [documentation index](docs/README.md) links the supporting material.

For quantum backflow and the work of Allcock and Bracken–Melloy, see the [Yearsley–Halliwell introduction](https://arxiv.org/abs/1301.4893). Further references are in the [bibliography](references.bib).
