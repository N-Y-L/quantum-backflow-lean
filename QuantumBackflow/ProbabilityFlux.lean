import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Probability transport for the free Schrödinger equation

The analytic hypotheses below are explicit conditions on the wavefunction and its derivatives.
Neither the continuity equation nor the probability-flux identity is assumed.  The constants
are arranged as `∂t ψ = c I ∂xx ψ` and `j = 2c Im(conj ψ ∂x ψ)`; physically `c = ℏ/(2m)`.
Probabilities are divided by the total squared norm, so the statements also apply to a
nonzero wavefunction before normalization.
-/

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

namespace QuantumBackflow

noncomputable section

/-- Position density before division by the total squared norm. -/
def density (ψ : ℝ → ℝ → ℂ) (t x : ℝ) : ℝ := Complex.normSq (ψ t x)

/-- Probability current for the convention `∂t ψ = c I ∂xx ψ`. -/
def current (c : ℝ) (ψ ψx : ℝ → ℝ → ℂ) (t x : ℝ) : ℝ :=
  2 * c * (conj (ψ t x) * ψx t x).im

/-- Explicit candidate for the time derivative of the density. -/
def densityRate (c : ℝ) (ψ ψxx : ℝ → ℝ → ℂ) (t x : ℝ) : ℝ :=
  -(2 * c * (conj (ψ t x) * ψxx t x).im)

/-- The unnormalized mass on the half-line to the left of `a`. -/
def leftMass (ψ : ℝ → ℝ → ℂ) (a t : ℝ) : ℝ := ∫ x in Iic a, density ψ t x

/-- Total squared norm. -/
def totalMass (ψ : ℝ → ℝ → ℂ) (t : ℝ) : ℝ := ∫ x, density ψ t x

/-- Born probability on the left half-line, for a nonzero square-integrable state. -/
def leftProbability (ψ : ℝ → ℝ → ℂ) (a t : ℝ) : ℝ :=
  leftMass ψ a t / totalMass ψ t

private theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (h : HasDerivAt f f' x) : HasDerivAt (fun y => (f y).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

private theorem hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (h : HasDerivAt f f' x) : HasDerivAt (fun y => (f y).im) f'.im x :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The free Schrödinger equation determines the time derivative of `|ψ|²`. -/
theorem hasDerivAt_density_of_schrodinger {c t x : ℝ} {ψ ψxx : ℝ → ℝ → ℂ}
    (ht : HasDerivAt (fun s => ψ s x) ((c : ℂ) * Complex.I * ψxx t x) t) :
    HasDerivAt (fun s => density ψ s x) (densityRate c ψ ψxx t x) t := by
  have hr := hasDerivAt_re ht
  have hi := hasDerivAt_im ht
  convert (hr.mul hr).add (hi.mul hi) using 1
  simp only [densityRate, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The spatial derivative of the current is the negative of the density's time derivative. -/
theorem hasDerivAt_current {c t x : ℝ} {ψ ψx ψxx : ℝ → ℝ → ℂ}
    (hx : HasDerivAt (ψ t) (ψx t x) x)
    (hxx : HasDerivAt (ψx t) (ψxx t x) x) :
    HasDerivAt (current c ψ ψx t) (-densityRate c ψ ψxx t x) x := by
  have h := (hasDerivAt_im (hx.star.mul hxx)).const_mul (2 * c)
  convert h using 1
  simp only [densityRate, neg_neg, Complex.add_im, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.star_def]
  ring

/-- Transparent regularity conditions that justify differentiation under the integral.
The time derivative is dominated on a neighborhood by a single integrable function.
The spatial assumptions and two decay assumptions are needed only at the time under study. -/
structure FluxRegularAt (c : ℝ) (ψ ψx ψxx : ℝ → ℝ → ℂ) (t₀ : ℝ) where
  neighborhood : Set ℝ
  neighborhood_mem : neighborhood ∈ 𝓝 t₀
  density_measurable : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (density ψ t)
  density_integrable : Integrable (density ψ t₀)
  rate_measurable : AEStronglyMeasurable (densityRate c ψ ψxx t₀)
  bound : ℝ → ℝ
  bound_integrable : Integrable bound
  rate_bound : ∀ᵐ x, ∀ t ∈ neighborhood, ‖densityRate c ψ ψxx t x‖ ≤ bound x
  schrodinger : ∀ᵐ x, ∀ t ∈ neighborhood,
    HasDerivAt (fun s => ψ s x) ((c : ℂ) * Complex.I * ψxx t x) t
  spatial_derivative : ∀ x, HasDerivAt (ψ t₀) (ψx t₀ x) x
  spatial_second_derivative : ∀ x, HasDerivAt (ψx t₀) (ψxx t₀ x) x
  current_atBot : Tendsto (current c ψ ψx t₀) atBot (𝓝 0)
  current_atTop : Tendsto (current c ψ ψx t₀) atTop (𝓝 0)

variable {c t₀ : ℝ} {ψ ψx ψxx : ℝ → ℝ → ℂ}

/-- Differentiation under an arbitrary restricted volume integral. -/
theorem FluxRegularAt.differentiate_integral (h : FluxRegularAt c ψ ψx ψxx t₀)
    (s : Set ℝ) :
    Integrable (densityRate c ψ ψxx t₀) (volume.restrict s) ∧
    HasDerivAt (fun t => ∫ x in s, density ψ t x)
      (∫ x in s, densityRate c ψ ψxx t₀ x) t₀ := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le h.neighborhood_mem
  · exact h.density_measurable.mono fun t ht => ht.restrict
  · exact h.density_integrable.restrict
  · exact h.rate_measurable.restrict
  · exact ae_restrict_of_ae h.rate_bound
  · exact h.bound_integrable.restrict
  · exact (ae_restrict_of_ae h.schrodinger).mono fun x hx t ht =>
      hasDerivAt_density_of_schrodinger (hx t ht)

/-- Born transport on a left half-line follows from local Schrödinger evolution and decay. -/
theorem FluxRegularAt.hasDerivAt_leftMass (h : FluxRegularAt c ψ ψx ψxx t₀) (a : ℝ) :
    HasDerivAt (leftMass ψ a) (-current c ψ ψx t₀ a) t₀ := by
  obtain ⟨hi, hd⟩ := h.differentiate_integral (Iic a)
  have hspace (x : ℝ) : HasDerivAt (fun y => -current c ψ ψx t₀ y)
      (densityRate c ψ ψxx t₀ x) x := by
    simpa using (hasDerivAt_current (h.spatial_derivative x)
      (h.spatial_second_derivative x)).neg
  have hlim : Tendsto (fun x => -current c ψ ψx t₀ x) atBot (𝓝 (0 : ℝ)) := by
    simpa using h.current_atBot.neg
  have hf := integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hspace x) hi hlim
  simpa only [sub_zero, leftMass, hf] using hd

/-- The same continuity equation conserves total mass to first order. -/
theorem FluxRegularAt.hasDerivAt_totalMass (h : FluxRegularAt c ψ ψx ψxx t₀) :
    HasDerivAt (totalMass ψ) 0 t₀ := by
  obtain ⟨hi, hd⟩ := h.differentiate_integral univ
  simp only [Measure.restrict_univ] at hi hd
  have hspace (x : ℝ) : HasDerivAt (fun y => -current c ψ ψx t₀ y)
      (densityRate c ψ ψxx t₀ x) x := by
    simpa using (hasDerivAt_current (h.spatial_derivative x)
      (h.spatial_second_derivative x)).neg
  have hb : Tendsto (fun x => -current c ψ ψx t₀ x) atBot (𝓝 (0 : ℝ)) := by
    simpa using h.current_atBot.neg
  have ht : Tendsto (fun x => -current c ψ ψx t₀ x) atTop (𝓝 (0 : ℝ)) := by
    simpa using h.current_atTop.neg
  have hf := integral_of_hasDerivAt_of_tendsto hspace hi hb ht
  simpa only [sub_self, totalMass, hf] using hd

/-- The normalized Born probability has derivative minus the normalized boundary current. -/
theorem FluxRegularAt.hasDerivAt_leftProbability (h : FluxRegularAt c ψ ψx ψxx t₀)
    (a : ℝ) (hM : totalMass ψ t₀ ≠ 0) :
    HasDerivAt (leftProbability ψ a) (-current c ψ ψx t₀ a / totalMass ψ t₀) t₀ := by
  convert (h.hasDerivAt_leftMass a).div h.hasDerivAt_totalMass hM using 1
  field_simp
  ring

/-- A continuous, nonzero square-integrable wavefunction has positive total squared norm. -/
theorem totalMass_pos {t x : ℝ} (hc : Continuous (ψ t))
    (hi : Integrable (density ψ t)) (hne : ψ t x ≠ 0) : 0 < totalMass ψ t := by
  apply integral_pos_of_integrable_nonneg_nonzero (f := density ψ t) (x := x)
    (Complex.continuous_normSq.comp hc) hi
  · exact fun y => Complex.normSq_nonneg _
  · exact fun hz => hne (Complex.normSq_eq_zero.mp hz)

/-- Half-line probabilities lie in the unit interval whenever the state has finite positive mass. -/
theorem leftProbability_mem_Icc {t a : ℝ} (hi : Integrable (density ψ t))
    (hM : 0 < totalMass ψ t) : leftProbability ψ a t ∈ Icc 0 1 := by
  have hl : 0 ≤ leftMass ψ a t := integral_nonneg fun x => Complex.normSq_nonneg _
  have hr : 0 ≤ ∫ x in (Iic a)ᶜ, density ψ t x :=
    integral_nonneg fun x => Complex.normSq_nonneg _
  have hs := integral_add_compl (s := Iic a) measurableSet_Iic hi
  have hle : leftMass ψ a t ≤ totalMass ψ t := by
    change leftMass ψ a t + (∫ x in (Iic a)ᶜ, density ψ t x) = totalMass ψ t at hs
    linarith
  exact ⟨div_nonneg hl hM.le, (div_le_one hM).2 hle⟩

/-- Positive derivative gives a strict probability gain for all sufficiently small positive times. -/
theorem eventually_increases_of_hasDerivAt_pos {f : ℝ → ℝ} {t d : ℝ}
    (hd : HasDerivAt f d t) (hpos : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f t < f (t + ε) := by
  have hs := hd.tendsto_slope_zero_right.eventually (eventually_gt_nhds hpos)
  filter_upwards [hs, self_mem_nhdsWithin] with ε hε hεpos
  have he : 0 < ε := hεpos
  have hq : 0 < (f (t + ε) - f t) / ε := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hε
  exact sub_pos.mp ((div_pos_iff_of_pos_right he).1 hq)

/-- Negative boundary current entails actual increase of the normalized left probability. -/
theorem FluxRegularAt.backflow (h : FluxRegularAt c ψ ψx ψxx t₀)
    (a : ℝ) (hM : 0 < totalMass ψ t₀) (hj : current c ψ ψx t₀ a < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), leftProbability ψ a t₀ < leftProbability ψ a (t₀ + ε) :=
  eventually_increases_of_hasDerivAt_pos (h.hasDerivAt_leftProbability a hM.ne')
    (div_pos (neg_pos.mpr hj) hM)

/-- The boundary point has zero Lebesgue measure, so the strict half-line is equivalent. -/
theorem leftMass_eq_integral_Iio (ψ : ℝ → ℝ → ℂ) (a t : ℝ) :
    leftMass ψ a t = ∫ x in Iio a, density ψ t x :=
  integral_Iic_eq_integral_Iio

/-- A useful absolute estimate for the local rate. -/
theorem norm_densityRate_le (c : ℝ) (ψ ψxx : ℝ → ℝ → ℂ) (t x : ℝ) :
    ‖densityRate c ψ ψxx t x‖ ≤ 2 * |c| * ‖ψ t x‖ * ‖ψxx t x‖ := by
  calc
    ‖densityRate c ψ ψxx t x‖ = 2 * |c| * |(conj (ψ t x) * ψxx t x).im| := by
      simp [densityRate, norm_mul]
    _ ≤ 2 * |c| * ‖conj (ψ t x) * ψxx t x‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by positivity)
    _ = _ := by rw [norm_mul, Complex.norm_conj]; ring

/-- A useful absolute estimate for the current. -/
theorem norm_current_le (c : ℝ) (ψ ψx : ℝ → ℝ → ℂ) (t x : ℝ) :
    ‖current c ψ ψx t x‖ ≤ 2 * |c| * ‖ψ t x‖ * ‖ψx t x‖ := by
  simpa only [densityRate, norm_neg, current] using norm_densityRate_le c ψ ψx t x

/-- A concrete interval formulation of the small-time probability gain. -/
theorem FluxRegularAt.backflow_interval (h : FluxRegularAt c ψ ψx ψxx t₀)
    (a : ℝ) (hM : 0 < totalMass ψ t₀) (hj : current c ψ ψx t₀ a < 0) :
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ,
      leftProbability ψ a t₀ < leftProbability ψ a (t₀ + ε) := by
  obtain ⟨δ, hδ, hh⟩ := Metric.mem_nhdsWithin_iff.mp (h.backflow a hM hj)
  refine ⟨δ, hδ, fun ε hε => hh ?_⟩
  exact ⟨by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
    abs_of_pos hε.1] using hε.2, hε.1⟩

end

end QuantumBackflow
