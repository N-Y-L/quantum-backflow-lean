# Proof guide

The theorem `QuantumBackflow.twoBand_backflow` in [`MainTheorem.lean`](../QuantumBackflow/MainTheorem.lean) proves the statement in the [README](../README.md#mathematical-statement). Its conclusion, `Backflow`, collects the wave's integrability, free evolution, mass conservation, and increasing left probability. The construction proceeds as follows.

## Spectrum and moments

[`Packets.lean`](../QuantumBackflow/Packets.lean) defines finite bands, their interfering superposition, and Born probabilities as ratios of squared-norm integrals. Disjointness gives

```math
\int|\phi|^2=(b-a)+r^2(e-d)>0.
```

The spectrum vanishes for every nonpositive wave number. Every polynomial spectral moment is integrable because the support is compact. The zeroth and first complex integrals reduce to the real quantities

```math
A=(b-a)-r(e-d),\qquad
B=(b^2-a^2)/2-r(e^2-d^2)/2.
```

The hypotheses $`A>0`$ and $`B<0`$ concern spectral moments. For the explicit profile $`\phi=\mathbf{1}_{[1,2]}-\frac{1}{2}\mathbf{1}_{[3,4]}`$, the squared norm is $`5/4`$; its normalized spectral representative is $`(2\mathbf{1}_{[1,2]}-\mathbf{1}_{[3,4]})/\sqrt{5}`$. The definition `exampleProfile` is $`2\phi`$. Scaling by a nonzero constant leaves Born probabilities unchanged.

## Free evolution and negative current

[`FreeEvolution.lean`](../QuantumBackflow/FreeEvolution.lean) defines

```math
\psi(t,x)=\int e^{i(kx-ck^2t)}\phi(k)\,dk.
```

Differentiation under the integral is justified by integrable spectral moments. Multiplication by $`ik`$ gives the spatial derivative, and multiplication by $`-ick^2`$ gives the time derivative. Thus the integral itself satisfies $`\partial_t\psi=ci\,\partial_x^2\psi`$.

[`BandEvolution.lean`](../QuantumBackflow/BandEvolution.lean) computes the current from these derivatives. At the origin,

```math
\psi(0,0)=A,\qquad \partial_x\psi(0,0)=iB,
\qquad j(0,0)=2cAB<0.
```

The explicit profile has $`A=1/2`$, $`B=-1/4`$, and current $`-c/4`$; `exampleProfile` has current $`-c`$. Free evolution multiplies the spectrum by a phase of modulus one, preserving its normalized wave-number distribution and positive physical-momentum probability.

## Spatial decay and integrability

[`FourierDecay.lean`](../QuantumBackflow/FourierDecay.lean) proves bounds for every polynomial band moment, uniformly over bounded time intervals. Integration by parts in the spectral variable yields

```math
\|F_k(t,x)\|\le C_k,\qquad |x|\|F_k(t,x)\|\le D_k.
```

Compactness supplies uniform bounds for the spectral amplitude and its derivative. [`BandRegularity.lean`](../QuantumBackflow/BandRegularity.lean) transfers these estimates to two-band waves and their first two spatial derivatives.

Combining these bounds gives

```math
\|z\|\|w\|\le\frac{C_zC_w+D_zD_w}{1+x^2}.
```

This controls the density, its time derivative, and the current. The function $`1/(1+x^2)`$ is integrable on the real line. These estimates also make the current tend to zero at both spatial infinities.

## From current to probability

[`ProbabilityFlux.lean`](../QuantumBackflow/ProbabilityFlux.lean) proves the continuity equation and differentiates the spatial integrals. [`DecayRegularity.lean`](../QuantumBackflow/DecayRegularity.lean) verifies the domination and boundary conditions using the decay bounds.

For total mass $`M`$ and left mass $`L`$, this gives

```math
M'(t)=0,\qquad L'(t)=-j(t,0),\qquad
P_-'(t)=-j(t,0)/M.
```

Nonvanishing at one point gives $`M>0`$; conservation extends this positivity to all times. Integrability and nonnegative density ensure $`0\le P_-\le1`$. The formal half-line uses $`x\le0`$; a proved measure-zero boundary identity gives the same probability for $`x<0`$.

Current continuity preserves strict negativity on an open interval. The normalized probability derivative is positive throughout that interval, and the mean-value theorem gives strict increase between every two ordered times in it.

## Normalization

The Fourier integral omits a normalization prefactor. In each representation, Born probabilities are integrals of squared modulus divided by the total squared norm. The position denominator is finite, positive, and time independent, and the normalized current is $`j/M`$.

Position mass conservation follows from the continuity equation and decay. The development does not prove Plancherel's identity relating spectral and position squared norms, a unitary Fourier transform, or the abstract spectral-measure construction of momentum. The generic regularity and flux lemmas state analytic hypotheses; the finite-band construction proves those hypotheses for `twoBand_backflow`.

## Arbitrary bands, time, boundary, and cutoff

[`ArbitraryBands.lean`](../QuantumBackflow/ArbitraryBands.lean) removes the moment-sign assumptions. Put $`u=b-a`$, $`v=e-d`$, $`s=a+b`$, and $`q=d+e`$. The coefficient

```math
r=\frac{u(s+q)}{2vq}
```

gives $`A=u(q-s)/(2q)>0`$ and $`B=u(s-q)/4<0`$. Hence `arbitraryBands_backflow` works for every $`0<a<b<d<e`$, and `chosenCoefficient_backflow` proves backflow with this coefficient.

`shifted_twoBand_backflow` multiplies the spectrum by a phase of modulus one to place backflow at any prescribed time and boundary. `quantum_backflow_exists` states existence at every such point, and `shifted_arbitraryBands_backflow` allows arbitrary separated positive bands. The phase preserves the momentum distribution.

[`Generalizations.lean`](../QuantumBackflow/Generalizations.lean) proves `quantum_backflow_above_cutoff`, with all spectral support above any finite cutoff. `quantum_backflow_with_probability_above_cutoff` gives the corresponding probability-one statement at every time. These theorems give no uniform lower bound on the amount or duration of backflow and do not determine the optimal Bracken–Melloy constant.

## References

The [Yearsley–Halliwell introduction](https://arxiv.org/abs/1301.4893) reviews quantum backflow and credits Allcock and Bracken–Melloy. [Yearsley et al.](https://journals.aps.org/pra/abstract/10.1103/PhysRevA.86.042116) give analytical examples. The [bibliography](../references.bib) also includes operator theory, scattering, repeated intervals, arbitrary momentum distributions, and alternative definitions. The present theorems concern the free-particle two-band construction; they do not prove those broader generalizations.
