# Prior-art and scope check

Search date: **13 September 2026**. This is a scoped public-source check, not a proof of priority.

## Finding

No existing machine-checked formalization of quantum backflow was identified in the searches below. This supports undertaking a Lean formalization, but does **not** establish that it is the first: unpublished work, unindexed repositories, differently named theorems, and other proof systems can escape these searches.

The physical phenomenon and substantial generalizations are established. A repository should claim only the mathematical statements its Lean files actually verify, with their hypotheses visible; it should not claim discovery of quantum backflow or new physics.

## Public repository search

The live GitHub REST repository search endpoint was queried with `per_page=100`. All successful search responses reported `incomplete_results=false`.

| Exact repository query | Results |
| --- | ---: |
| `quantum backflow` | 6 |
| `backflow language:Lean` | 0 |
| `backflow language:Coq` | 0 |
| `backflow language:Isabelle` | 0 |
| `backflow HOL` | 0 |
| `backflow Rocq` | 0 |

The six returned repositories were inspected through their default-branch file trees:

| Repository | Observed contents |
| --- | --- |
| [petrusyuri/quantumbackflow](https://github.com/petrusyuri/quantumbackflow) | Fortran numerical code |
| [UKVeteran/Quantum-Backflow](https://github.com/UKVeteran/Quantum-Backflow) | README and figure images |
| [Alexandre-Hefren/Backflow_Defects](https://github.com/Alexandre-Hefren/Backflow_Defects) | Fortran numerical code |
| [mnbjhu/Quantum_Backflow_Approximation](https://github.com/mnbjhu/Quantum_Backflow_Approximation) | File-tree request returned HTTP 409; contents not established |
| [UKVeteran/Quantum-Backflow-Effect](https://github.com/UKVeteran/Quantum-Backflow-Effect) | MATLAB code and numerical data |
| [hkk506/Repeated-quantum-backflow-and-quantum-overflow](https://github.com/hkk506/Repeated-quantum-backflow-and-quantum-overflow) | Python/Maple spectral estimates and supporting data |

No `.lean`, `.v`, `.thy`, or `.sml` files occurred in the five accessible trees; those trees were not truncated. This distinguishes the observed numerical implementations from proof-assistant verification. The public [PhysLean/physlib](https://github.com/leanprover-community/physlib) tree also contained no path mentioning `backflow` (847 Lean files observed). Only its paths were checked; this is not a content-level absence proof.

Repository search covers repository metadata, not an exhaustive global search of theorem bodies. Authenticated global GitHub code search was not performed.

## Supplementary indexed searches

The following exact search strings produced no identifiable proof-assistant formalization:

```text
"quantum backflow" Lean formalization
"quantum backflow" Coq Isabelle HOL formal proof
"quantum backflow" "proof assistant"
"quantum backflow" "Lean 4"
"quantum backflow" "Isabelle"
"quantum backflow" "Coq"
"backflow" "Rocq"
"backflow" "HOL Light"
"backflow" "Isabelle/HOL" quantum
"backflow" "mathlib"
site:github.com "backflow" "lean"
site:github.com "quantum backflow"
site:isa-afp.org backflow
"backflow" "formalization" quantum
```

Some results concerned unrelated network, fluid, or information backflow. These are not evidence about probability transport of a free particle. An attempted direct AFP physics-topic URL failed to load, so no complete AFP corpus inspection is claimed.

## Established mathematical and physical literature

- **Original effect.** Bracken and Melloy, *Probability backflow and a new dimensionless quantum number* (1994), systematically studied positive-momentum states with backward probability transfer. Earlier work is credited to Allcock (1969). The [Yearsley–Halliwell introduction](https://arxiv.org/abs/1301.4893) gives the standard current/half-line probability relation and historical references. The [2012 analytical study](https://journals.aps.org/pra/abstract/10.1103/PhysRevA.86.042116) constructs tractable backflow states. Ordinary Gaussian packets have small but nonzero negative-momentum tails, so they cannot establish the exact hypothesis `Pr(p > 0) = 1` without an additional argument or altered construction.
- **Rigorous operator theory.** [Penz, Grübl, Kreidl, and Wagner](https://arxiv.org/abs/quant-ph/0511109) prove that the backflow operator is bounded, self-adjoint, and noncompact. Their numerical calculation is distinct from a machine-checked formal proof.
- **Scattering generalization.** [Bostelmann, Cadamuro, and Lechner](https://arxiv.org/abs/1703.04597) extend backflow to short-range scattering potentials. “Generalized backflow” is therefore not itself a novelty claim.
- **Repeated intervals.** [Fewster and Kirk-Karakaya](https://arxiv.org/abs/2505.13184) study sums over disjoint time intervals, repeated backflow, and overflow; their linked repository supplies numerical computations.
- **Arbitrary momentum distributions.** [Paterek and Goussev](https://arxiv.org/html/2511.10155v2), published in 2026, define general backflow through a violation of the classical inequality `P_-(t₂) − P_-(t₁) ≤ Pr(p < 0)`, for `t₁ < t₂`. This includes strictly positive momentum as a special case. Their generalization and quantitative bounds must be credited if reused.
- **Different generalized definitions need care.** The [2021 experiment-friendly formulation](https://quantum-journal.org/papers/q-2021-01-11-379/) and [Barbier–Goussev response](https://quantum-journal.org/papers/q-2021-09-07-536/) show why distinct definitions should not be silently identified.

Bibliographic records are in [`references.bib`](../references.bib).

## Continuum construction used here

The following elementary construction is used in the formalization; no claim that the example or its general form is new is intended. With wave number `k` and positive free-evolution coefficient `c`, use

\[
\phi(k)=\mathbf 1_{[1,2]}(k)-\tfrac12\mathbf 1_{[3,4]}(k),\qquad
\psi(t,x)=\int_{\mathbb R}e^{i(kx-ck^2t)}\phi(k)\,dk.
\]

The spectrum has compact strictly positive support and squared norm `5/4`. Its zeroth and first moments are `1/2` and `−1/4`. The unnormalized boundary current is therefore

\[
j(0,0)=2c\operatorname{Re}(\overline{M_0}M_1)=-c/4<0.
\]

The physical convention is `c = ℏ/(2m)` and physical momentum is `ℏ k`. Born probabilities divide each representation's squared-density integral by its total squared norm. The normalized spectral representative is `(2·1_[1,2] − 1_[3,4])/√5`.

The general theorem allows unequal band widths. For every `0<a<b<d<e`, an explicit coefficient in `1_[a,b] − r 1_[d,e]` makes the zeroth moment positive and the first moment negative. The construction can be translated to any spacetime point and placed above any finite spectral cutoff. These are square-integrable continuum wave packets; nonnormalizable plane waves and Gaussian negative-momentum tails are not used.

The [proof guide](proof-guide.md) explains how the spectral construction, actual free evolution, spatial decay, positive conserved position mass, and normalized probability derivative are connected. The normalization is projective: a Plancherel identity between the numerical spectral and spatial masses is not part of the formalized result. The generalization concerns the constructive two-band family; it does not reproduce the arbitrary-momentum or repeated-interval results cited above.
