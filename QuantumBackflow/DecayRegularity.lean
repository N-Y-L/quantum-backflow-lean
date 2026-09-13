import QuantumBackflow.ProbabilityFlux
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FunProp

/-!
# Uniform Fourier decay implies the analytic hypotheses for probability transport

The boundedness assumptions below are the elementary estimates obtained by integration by
parts for finite momentum bands.  They imply integrable squared density and an integrable
uniform bound on the time derivative of that density.  They also force the current to vanish
at both spatial infinities.  Consequently the abstract probability-flux theorem is fully
applicable, total mass is conserved, and any negative current persists on an open interval.
-/

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

noncomputable section
namespace QuantumBackflow

/-- An elementary integrable envelope produced by a bounded function and bounded `x*f(x)`. -/
def decayEnvelope (K x : ℝ) : ℝ := 2 * K ^ 2 / (1 + x ^ 2)

lemma decayEnvelope_nonneg (K x : ℝ) : 0 ≤ decayEnvelope K x := by
  unfold decayEnvelope
  positivity

lemma integrable_decayEnvelope (K : ℝ) : Integrable (decayEnvelope K) := by
  simpa only [decayEnvelope, div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (2*K^2)

lemma normSq_le_decayEnvelope {z : ℂ} {K x : ℝ} (hK : 0 ≤ K)
    (hz : ‖z‖ ≤ K) (hxz : |x| * ‖z‖ ≤ K) :
    Complex.normSq z ≤ decayEnvelope K x := by
  have hz2 : ‖z‖ ^ 2 ≤ K ^ 2 := by nlinarith [norm_nonneg z]
  have hxz2 : (|x| * ‖z‖) ^ 2 ≤ K ^ 2 := by
    nlinarith [mul_nonneg (abs_nonneg x) (norm_nonneg z)]
  rw [mul_pow, sq_abs] at hxz2
  rw [Complex.normSq_eq_norm_sq, decayEnvelope, le_div_iff₀ (by positivity)]
  nlinarith

lemma norm_mul_le_decayEnvelope {z w : ℂ} {K x : ℝ} (hK : 0 ≤ K)
    (hz : ‖z‖ ≤ K) (hxz : |x| * ‖z‖ ≤ K)
    (hw : ‖w‖ ≤ K) (hxw : |x| * ‖w‖ ≤ K) :
    ‖z‖ * ‖w‖ ≤ decayEnvelope K x := by
  have hz2 := normSq_le_decayEnvelope hK hz hxz
  have hw2 := normSq_le_decayEnvelope hK hw hxw
  rw [Complex.normSq_eq_norm_sq] at hz2 hw2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma tendsto_decayEnvelope_atTop (K : ℝ) :
    Tendsto (decayEnvelope K) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_atTop_mono (fun x : ℝ => by linarith : ∀ x : ℝ, x^2 ≤ 1+x^2)
    (tendsto_pow_atTop (n := 2) (by norm_num))

lemma tendsto_decayEnvelope_atBot (K : ℝ) :
    Tendsto (decayEnvelope K) atBot (𝓝 0) := by
  simpa only [Function.comp_def, decayEnvelope, neg_sq] using
    (tendsto_decayEnvelope_atTop K).comp tendsto_neg_atBot_atTop

/-- Uniform bounds on each wavefunction derivative on every bounded time interval. -/
def UniformWaveDecay (ψ ψx ψxx : ℝ → ℝ → ℂ) : Prop :=
  ∀ T > 0, ∃ K ≥ 0, ∀ t, |t| ≤ T → ∀ x,
    (‖ψ t x‖ ≤ K ∧ |x| * ‖ψ t x‖ ≤ K) ∧
    (‖ψx t x‖ ≤ K ∧ |x| * ‖ψx t x‖ ≤ K) ∧
    (‖ψxx t x‖ ≤ K ∧ |x| * ‖ψxx t x‖ ≤ K)

/-- Classical free Schrödinger evolution with the explicit decay available for finite bands. -/
structure SchrodingerRegular (c : ℝ) (ψ ψx ψxx : ℝ → ℝ → ℂ) : Prop where
  continuous_wave : Continuous (Function.uncurry ψ)
  continuous_first : Continuous (Function.uncurry ψx)
  continuous_second : Continuous (Function.uncurry ψxx)
  schrodinger : ∀ t x, HasDerivAt (fun s => ψ s x) ((c : ℂ)*Complex.I*ψxx t x) t
  spatial_derivative : ∀ t x, HasDerivAt (ψ t) (ψx t x) x
  spatial_second_derivative : ∀ t x, HasDerivAt (ψx t) (ψxx t x) x
  uniform_decay : UniformWaveDecay ψ ψx ψxx

variable {c : ℝ} {ψ ψx ψxx : ℝ → ℝ → ℂ}

lemma SchrodingerRegular.continuous_density (h : SchrodingerRegular c ψ ψx ψxx) (t : ℝ) :
    Continuous (density ψ t) :=
  Complex.continuous_normSq.comp (h.continuous_wave.comp (continuous_const.prodMk continuous_id))

lemma SchrodingerRegular.continuous_densityRate (h : SchrodingerRegular c ψ ψx ψxx)
    (t : ℝ) : Continuous (densityRate c ψ ψxx t) := by
  have hw : Continuous (ψ t) := h.continuous_wave.comp (continuous_const.prodMk continuous_id)
  have hxx : Continuous (ψxx t) := h.continuous_second.comp (continuous_const.prodMk continuous_id)
  unfold densityRate
  fun_prop

lemma SchrodingerRegular.continuous_current (h : SchrodingerRegular c ψ ψx ψxx)
    (a : ℝ) : Continuous (fun t => current c ψ ψx t a) := by
  have hw : Continuous (fun t => ψ t a) :=
    h.continuous_wave.comp (continuous_id.prodMk continuous_const)
  have hx : Continuous (fun t => ψx t a) :=
    h.continuous_first.comp (continuous_id.prodMk continuous_const)
  unfold current
  fun_prop

/-- No flux or probability assumption appears in this bridge from elementary decay estimates. -/
def SchrodingerRegular.fluxRegularAt (h : SchrodingerRegular c ψ ψx ψxx) (t₀ : ℝ) :
    FluxRegularAt c ψ ψx ψxx t₀ := by
  classical
  let hex := h.uniform_decay (|t₀|+1) (by positivity)
  let K := Classical.choose hex
  have hK : 0 ≤ K := (Classical.choose_spec hex).1
  have hb := (Classical.choose_spec hex).2
  have ht₀ : |t₀| ≤ |t₀|+1 := by linarith
  have hden (x : ℝ) : density ψ t₀ x ≤ decayEnvelope K x :=
    normSq_le_decayEnvelope hK (hb t₀ ht₀ x).1.1 (hb t₀ ht₀ x).1.2
  have hrate (t x : ℝ) (ht : |t| ≤ |t₀|+1) :
      ‖densityRate c ψ ψxx t x‖ ≤ 2*|c| *decayEnvelope K x := by
    calc
      _ ≤ 2*|c| *‖ψ t x‖*‖ψxx t x‖ := norm_densityRate_le _ _ _ _ _
      _ = 2*|c| *(‖ψ t x‖*‖ψxx t x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (norm_mul_le_decayEnvelope hK (hb t ht x).1.1 (hb t ht x).1.2
          (hb t ht x).2.2.1 (hb t ht x).2.2.2) (by positivity)
  have hj (x : ℝ) : ‖current c ψ ψx t₀ x‖ ≤ 2*|c| *decayEnvelope K x := by
    calc
      _ ≤ 2*|c| *‖ψ t₀ x‖*‖ψx t₀ x‖ := norm_current_le _ _ _ _ _
      _ = 2*|c| *(‖ψ t₀ x‖*‖ψx t₀ x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (norm_mul_le_decayEnvelope hK (hb t₀ ht₀ x).1.1 (hb t₀ ht₀ x).1.2
          (hb t₀ ht₀ x).2.1.1 (hb t₀ ht₀ x).2.1.2) (by positivity)
  refine {
    neighborhood := Ioo (t₀-1) (t₀+1)
    neighborhood_mem := Ioo_mem_nhds (by linarith) (by linarith)
    density_measurable := Eventually.of_forall fun t => (h.continuous_density t).aestronglyMeasurable
    density_integrable := ?_
    rate_measurable := (h.continuous_densityRate t₀).aestronglyMeasurable
    bound := fun x => 2*|c| *decayEnvelope K x
    bound_integrable := (integrable_decayEnvelope K).const_mul _
    rate_bound := ?_
    schrodinger := Eventually.of_forall fun x t _ => h.schrodinger t x
    spatial_derivative := h.spatial_derivative t₀
    spatial_second_derivative := h.spatial_second_derivative t₀
    current_atBot := ?_
    current_atTop := ?_ }
  · apply (integrable_decayEnvelope K).mono' (h.continuous_density t₀).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simpa only [density, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)] using hden x
  · exact Eventually.of_forall fun x t ht => hrate t x (abs_le.mpr
      ⟨by linarith [neg_abs_le t₀, ht.1], by linarith [le_abs_self t₀, ht.2]⟩)
  · apply squeeze_zero_norm hj
    simpa using (tendsto_decayEnvelope_atBot K).const_mul (2*|c|)
  · apply squeeze_zero_norm hj
    simpa using (tendsto_decayEnvelope_atTop K).const_mul (2*|c|)

/-- Global mass conservation, obtained from the previously proved local continuity equation. -/
theorem SchrodingerRegular.totalMass_eq (h : SchrodingerRegular c ψ ψx ψxx) (t s : ℝ) :
    totalMass ψ t = totalMass ψ s := by
  apply is_const_of_deriv_eq_zero
  · exact fun u => (h.fluxRegularAt u).hasDerivAt_totalMass.differentiableAt
  · exact fun u => (h.fluxRegularAt u).hasDerivAt_totalMass.deriv

/-- Nontriviality at one spacetime point gives positive conserved mass at every time. -/
theorem SchrodingerRegular.totalMass_pos (h : SchrodingerRegular c ψ ψx ψxx)
    {s x : ℝ} (hne : ψ s x ≠ 0) (t : ℝ) : 0 < totalMass ψ t := by
  rw [h.totalMass_eq t s]
  exact QuantumBackflow.totalMass_pos
    (h.continuous_wave.comp (continuous_const.prodMk continuous_id))
    (h.fluxRegularAt s).density_integrable hne

/-- Negative current persists, producing a full open interval of positive probability derivative
and strict increase between every two times in that interval. -/
theorem SchrodingerRegular.backflow_open_interval (h : SchrodingerRegular c ψ ψx ψxx)
    {a t₀ : ℝ} (hM : 0 < totalMass ψ t₀) (hj : current c ψ ψx t₀ a < 0) :
    ∃ δ > 0,
      (∀ t ∈ Ioo (t₀-δ) (t₀+δ), 0 < deriv (leftProbability ψ a) t) ∧
      StrictMonoOn (leftProbability ψ a) (Ioo (t₀-δ) (t₀+δ)) := by
  have hm (t : ℝ) : 0 < totalMass ψ t := by rw [h.totalMass_eq t t₀]; exact hM
  have hd (t : ℝ) := (h.fluxRegularAt t).hasDerivAt_leftProbability a (hm t).ne'
  have hn : ∀ᶠ t in 𝓝 t₀, current c ψ ψx t a < 0 :=
    (h.continuous_current a).continuousAt.eventually (eventually_lt_nhds hj)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hn
  have hder (t : ℝ) (ht : t ∈ Ioo (t₀-δ) (t₀+δ)) :
      0 < deriv (leftProbability ψ a) t := by
    rw [(hd t).deriv]
    apply div_pos (neg_pos.mpr (hh ?_)) (hm t)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨δ, hδ, hder, ?_⟩
  exact strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t ht => hder t (interior_subset ht))

/-- A negative current itself certifies a nonzero state, so no separate mass hypothesis is needed. -/
theorem SchrodingerRegular.backflow_of_current_neg (h : SchrodingerRegular c ψ ψx ψxx)
    {a t₀ : ℝ} (hj : current c ψ ψx t₀ a < 0) :
    ∃ δ > 0,
      (∀ t ∈ Ioo (t₀-δ) (t₀+δ), 0 < deriv (leftProbability ψ a) t) ∧
      StrictMonoOn (leftProbability ψ a) (Ioo (t₀-δ) (t₀+δ)) := by
  have hne : ψ t₀ a ≠ 0 := by
    intro hz
    simp only [current, hz, map_zero, zero_mul, Complex.zero_im, mul_zero, lt_self_iff_false] at hj
  exact h.backflow_open_interval (h.totalMass_pos hne t₀) hj

/-- The conserved nonzero wavefunction gives valid Born probabilities at every time and boundary. -/
theorem SchrodingerRegular.probability_mem_Icc (h : SchrodingerRegular c ψ ψx ψxx)
    {s x : ℝ} (hne : ψ s x ≠ 0) (a t : ℝ) : leftProbability ψ a t ∈ Icc 0 1 :=
  leftProbability_mem_Icc (h.fluxRegularAt t).density_integrable (h.totalMass_pos hne t)

end QuantumBackflow
