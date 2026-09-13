# Proof guide

The central theorem is `QuantumBackflow.twoBand_backflow` in [`MainTheorem.lean`](../QuantumBackflow/MainTheorem.lean). Its conclusion, `Backflow`, collects the analytic and probabilistic properties of the actual freely evolving two-band state. `explicit_quantum_backflow` supplies concrete band endpoints and coefficient.

## 1. Spectrum and exact moments

[`Packets.lean`](../QuantumBackflow/Packets.lean) defines finite bands, their interfering superposition, and Born probabilities as ratios of squared-norm integrals. Disjointness gives

\[
\int|\phi|^2=(b-a)+r^2(e-d)>0.
\]

The spectrum vanishes for every nonpositive wave number. Every polynomial spectral moment is integrable because the support is compact. The zeroth and first complex integrals reduce to the real quantities

\[
A=(b-a)-r(e-d),\qquad
B=(b^2-a^2)/2-r(e^2-d^2)/2.
\]

The hypotheses `A > 0` and `B < 0` concern computable spectral moments. They do not assume backflow.

## 2. Actual free evolution and negative current

[`FreeEvolution.lean`](../QuantumBackflow/FreeEvolution.lean) defines

\[
\psi(t,x)=\int e^{i(kx-ck^2t)}\phi(k)\,dk.
\]

Differentiation under the integral is justified by integrable spectral moments. Multiplication by `ik` gives the spatial derivative, and multiplication by `−ick²` gives the time derivative. Thus the integral itself satisfies `∂t ψ = ci ∂xx ψ`.

[`BandEvolution.lean`](../QuantumBackflow/BandEvolution.lean) computes the current from these derivatives. At the origin,

\[
\psi(0,0)=A,\qquad \partial_x\psi(0,0)=iB,
\qquad j(0,0)=2cAB<0.
\]

Free evolution multiplies the spectrum by a phase of modulus one. Its entire normalized wave-number distribution, and hence positive physical-momentum probability, is unchanged.

## 3. Spatial decay and integrability

[`FourierDecay.lean`](../QuantumBackflow/FourierDecay.lean) proves bounds for every polynomial band moment, uniformly over bounded time intervals. Integration by parts in the spectral variable yields

\[
\|F_k(t,x)\|\le C_k,\qquad |x|\|F_k(t,x)\|\le D_k.
\]

The constants need not be optimal. Compactness supplies uniform bounds for the spectral amplitude and its derivative. [`BandRegularity.lean`](../QuantumBackflow/BandRegularity.lean) transfers these estimates to two-band waves and their first two spatial derivatives.

Combining ordinary and frequency-weighted bounds gives an everywhere valid majorant:

\[
\|z\|\|w\|\le\frac{C_zC_w+D_zD_w}{1+x^2}.
\]

This controls the density, its time derivative, and the current. The denominator is integrable on the real line. These estimates also make the current tend to zero at both spatial infinities.

## 4. From current to normalized probability

[`ProbabilityFlux.lean`](../QuantumBackflow/ProbabilityFlux.lean) proves the continuity equation and differentiates the actual spatial integrals. [`DecayRegularity.lean`](../QuantumBackflow/DecayRegularity.lean) verifies the needed domination and boundary conditions from the preceding decay bounds.

For total mass `M` and left mass `L`, this gives

\[
M'(t)=0,\qquad L'(t)=-j(t,0),\qquad
P_-'(t)=-j(t,0)/M.
\]

Nonvanishing at one point gives `M > 0`; conservation extends this positivity to all times. Integrability and nonnegative density ensure `0 ≤ P_- ≤ 1`. The formal half-line uses `x ≤ 0`; a proved measure-zero boundary identity gives the same probability for `x < 0`.

Finally, current continuity preserves strict negativity on an open interval. The normalized probability derivative is positive throughout that interval. The mean-value argument yields strict increase between every two ordered times in it, rather than only a single finite-time gain.

## 5. Scope of normalization

The omitted Fourier prefactor is handled through Born ratios. Both representations are separately normalized; the position denominator is proved to be finite, positive, and time independent. The development does not prove the Plancherel identity relating the numerical values of the two unnormalized squared norms. Consequently it makes no claim to a formalized unitary Fourier transform or abstract spectral-measure construction.

Read the instantiated theorem in `MainTheorem.lean` when assessing the result. The generic regularity and flux lemmas deliberately expose analytic hypotheses; they become a concrete backflow theorem only after the finite-band construction discharges those hypotheses.

## 6. Generalized existence

[`ArbitraryBands.lean`](../QuantumBackflow/ArbitraryBands.lean) removes the moment-sign assumptions. Put `u=b−a`, `v=e−d`, `s=a+b`, and `t=d+e`. The coefficient

\[
r=\frac{u(s+t)}{2vt}
\]

gives `A=u(t−s)/(2t)>0` and `B=u(s−t)/4<0`. Hence `arbitraryBands_backflow` works for every `0<a<b<d<e`, and `chosenCoefficient_backflow` identifies the explicit witness.

`shifted_twoBand_backflow` uses a unit-modulus spectral phase to move a witness to any prescribed time and boundary. `quantum_backflow_exists` states the resulting unrestricted spacetime existence, and `shifted_arbitraryBands_backflow` combines it with arbitrary chosen bands. The momentum distribution is unchanged by this phase.

Finally, [`Generalizations.lean`](../QuantumBackflow/Generalizations.lean) proves `quantum_backflow_above_cutoff`: backflow remains possible with all spectral support above any finite cutoff. This is an existence assertion, not a bound uniform in the cutoff on the amount or duration of backflow.
