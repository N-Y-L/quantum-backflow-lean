import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

open MeasureTheory Filter Complex
open scoped Topology

noncomputable section

namespace QuantumBackflow

/-- A unit-modulus phase, in the convention with no Fourier normalization factor. -/
def phase (y : ℝ) : ℂ := Complex.exp ((y : ℂ) * I)

@[simp] theorem norm_phase (y : ℝ) : ‖phase y‖ = 1 := by
  simp [phase, Complex.norm_exp]

@[fun_prop] theorem continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

lemma hasDerivAt_phase (y : ℝ) : HasDerivAt phase (phase y * I) y := by
  simpa [phase] using (((hasDerivAt_id y).ofReal_comp.mul_const I).cexp)

/-- Integrability is unchanged by multiplication by a real phase. -/
lemma integrable_phase_mul {φ : ℝ → ℂ} (hφ : Integrable φ)
    {θ : ℝ → ℝ} (hθ : Measurable θ) :
    Integrable (fun p => phase (θ p) * φ p) := by
  apply Integrable.mono' hφ.norm
    ((continuous_phase.measurable.comp hθ).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  filter_upwards [] with p
  simp

/-- Differentiation of an oscillatory integral with an integrable first moment. -/
lemma hasDerivAt_phase_integral {φ : ℝ → ℂ} {θ ω : ℝ → ℝ}
    (hφ : Integrable φ) (hθ : Measurable θ) (hω : Measurable ω)
    (hωφ : Integrable (fun p => (ω p : ℂ) * φ p)) (y : ℝ) :
    HasDerivAt (fun z => ∫ p, phase (θ p + ω p * z) * φ p)
      (∫ p, phase (θ p + ω p * y) * ((ω p : ℂ) * I * φ p)) y := by
  have hmoment : Integrable (fun p => (ω p : ℂ) * I * φ p) := by
    convert hωφ.mul_const I using 1
    ext p
    ring
  have hi (z : ℝ) := integrable_phase_mul hφ (hθ.add (hω.mul measurable_const)) (θ := fun p => θ p + ω p * z)
  have hid (z : ℝ) := integrable_phase_mul hmoment (hθ.add (hω.mul measurable_const)) (θ := fun p => θ p + ω p * z)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (bound := fun p => ‖(ω p : ℂ) * I * φ p‖)
    (by simp) (Filter.Eventually.of_forall fun z => (hi z).aestronglyMeasurable)
    (hi y) (hid y).aestronglyMeasurable ?_ hmoment.norm ?_).2
  · filter_upwards [] with p z _
    simp
  · filter_upwards [] with p z _
    convert ((hasDerivAt_phase (θ p + ω p * z)).scomp z
      ((hasDerivAt_const z (θ p)).add ((hasDerivAt_id z).const_mul (ω p)))).mul_const (φ p) using 1
    simp only [zero_add, mul_one, Complex.real_smul]
    ring

/-- Free evolution of a spectral amplitude. The variable is wave number and c = ℏ/(2m). -/
def wave (c : ℝ) (φ : ℝ → ℂ) (t x : ℝ) : ℂ :=
  ∫ p, phase (p * x - c * p ^ 2 * t) * φ p

/-- The momentum amplitude representing the spatial derivative. -/
def momentumDerivative (φ : ℝ → ℂ) (p : ℝ) : ℂ := (p : ℂ) * I * φ p

/-- Probability momentumCurrent corresponding to the chosen Fourier convention. -/
def momentumCurrent (c : ℝ) (φ : ℝ → ℂ) (t x : ℝ) : ℝ :=
  2 * c * (star (wave c φ t x) * wave c (momentumDerivative φ) t x).im

lemma hasDerivAt_wave_space (c : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hpφ : Integrable (fun p : ℝ => (p : ℂ) * φ p)) (t x : ℝ) :
    HasDerivAt (wave c φ t) (wave c (momentumDerivative φ) t x) x := by
  unfold wave
  convert hasDerivAt_phase_integral hφ
    (θ := fun p => -(c * p ^ 2 * t)) (ω := fun p => p)
    (by fun_prop) measurable_id hpφ x using 1 <;>
    simp only [momentumDerivative, sub_eq_add_neg, add_comm]

lemma hasDerivAt_wave_time (c : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hp2φ : Integrable (fun p : ℝ => (p : ℂ)^2 * φ p)) (t x : ℝ) :
    HasDerivAt (fun s => wave c φ s x)
      (wave c (fun p => -((c : ℂ) * I) * ((p : ℂ)^2 * φ p)) t x) t := by
  have hωφ : Integrable (fun p : ℝ => ((-(c * p^2) : ℝ) : ℂ) * φ p) := by
    convert hp2φ.const_mul (-(c : ℂ)) using 1
    ext p
    push_cast
    ring
  unfold wave
  convert hasDerivAt_phase_integral hφ
    (θ := fun p => p*x) (ω := fun p => -(c*p^2))
    (by fun_prop) (by fun_prop) hωφ t using 1
  · funext s
    congr 1
    funext p
    congr 2
    ring
  · congr 1
    ext p
    congr 1
    · congr 1
      ring
    · push_cast
      ring

lemma integrable_momentumDerivative {φ : ℝ → ℂ}
    (hpφ : Integrable (fun p : ℝ => (p : ℂ) * φ p)) :
    Integrable (momentumDerivative φ) := by
  convert hpφ.mul_const I using 1
  ext p
  unfold momentumDerivative
  ring

lemma wave_const_mul (c : ℝ) (φ : ℝ → ℂ) (z : ℂ) (t x : ℝ) :
    wave c (fun p => z * φ p) t x = z * wave c φ t x := by
  simp only [wave, ← integral_const_mul]
  congr 1
  funext p
  ring

lemma momentumDerivative_twice (φ : ℝ → ℂ) :
    momentumDerivative (momentumDerivative φ) = fun p : ℝ => -((p : ℂ)^2 * φ p) := by
  funext p
  simp only [momentumDerivative]
  calc
    _ = (I * I) * ((p : ℂ)^2 * φ p) := by ring
    _ = _ := by simp

/-- The second spatial derivative under the integrable second-moment hypothesis. -/
lemma hasDerivAt_wave_space_twice (c : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hpφ : Integrable (fun p : ℝ => (p : ℂ) * φ p))
    (hp2φ : Integrable (fun p : ℝ => (p : ℂ)^2 * φ p)) (t x : ℝ) :
    HasDerivAt (deriv (wave c φ t))
      (wave c (fun p : ℝ => -((p : ℂ)^2 * φ p)) t x) x := by
  have hderiv : deriv (wave c φ t) = wave c (momentumDerivative φ) t := by
    funext y
    exact (hasDerivAt_wave_space c hφ hpφ t y).deriv
  rw [hderiv]
  have hmoment : Integrable (fun p : ℝ => (p : ℂ) * momentumDerivative φ p) := by
    convert hp2φ.mul_const I using 1
    ext p
    simp only [momentumDerivative]
    ring
  simpa only [momentumDerivative_twice] using
    hasDerivAt_wave_space c (integrable_momentumDerivative hpφ) hmoment t x

/-- A derivative statement in a form convenient for probability-flux identities. -/
lemma hasDerivAt_wave_space_derivative (c : ℝ) {φ : ℝ → ℂ}
    (hpφ : Integrable (fun p : ℝ => (p : ℂ) * φ p))
    (hp2φ : Integrable (fun p : ℝ => (p : ℂ)^2 * φ p)) (t x : ℝ) :
    HasDerivAt (wave c (momentumDerivative φ) t)
      (wave c (momentumDerivative (momentumDerivative φ)) t x) x := by
  have hmoment : Integrable (fun p : ℝ => (p : ℂ) * momentumDerivative φ p) := by
    convert hp2φ.mul_const I using 1
    ext p
    simp only [momentumDerivative]
    ring
  exact hasDerivAt_wave_space c (integrable_momentumDerivative hpφ) hmoment t x

/-- The free equation expressed directly as a time derivative. -/
lemma schrodinger_time (c : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hp2φ : Integrable (fun p : ℝ => (p : ℂ)^2 * φ p)) (t x : ℝ) :
    HasDerivAt (fun s => wave c φ s x)
      ((c : ℂ)*I*wave c (momentumDerivative (momentumDerivative φ)) t x) t := by
  convert hasDerivAt_wave_time c hφ hp2φ t x using 1
  rw [momentumDerivative_twice, ← wave_const_mul]
  congr 1
  funext p
  ring

/-- This integral is an actual solution of the ordinary free Schrödinger equation. -/
theorem free_schrodinger (c : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hpφ : Integrable (fun p : ℝ => (p : ℂ) * φ p))
    (hp2φ : Integrable (fun p : ℝ => (p : ℂ)^2 * φ p)) (t x : ℝ) :
    I * deriv (fun s => wave c φ s x) t =
      -(c : ℂ) * deriv (deriv (wave c φ t)) x := by
  rw [(hasDerivAt_wave_time c hφ hp2φ t x).deriv,
    (hasDerivAt_wave_space_twice c hφ hpφ hp2φ t x).deriv, wave_const_mul]
  have hneg : wave c (fun p : ℝ => -((p : ℂ)^2 * φ p)) t x =
      -(wave c (fun p : ℝ => (p : ℂ)^2 * φ p) t x) := by
    simpa only [neg_one_mul] using wave_const_mul c (fun p : ℝ => (p : ℂ)^2 * φ p) (-1) t x
  rw [hneg]
  calc
    _ = -(c : ℂ) * (I * I) * wave c (fun p : ℝ => (p : ℂ)^2 * φ p) t x := by ring
    _ = _ := by simp

/-- Joint space-time continuity requires only integrability of the amplitude. -/
lemma continuous_wave (c : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) :
    Continuous (fun tx : ℝ × ℝ => wave c φ tx.1 tx.2) := by
  unfold wave
  apply continuous_of_dominated (bound := fun p => ‖φ p‖)
  · intro tx
    exact (integrable_phase_mul hφ (by fun_prop)).aestronglyMeasurable
  · intro tx
    filter_upwards [] with p
    simp
  · exact hφ.norm
  · filter_upwards [] with p
    fun_prop

lemma continuous_momentumCurrent (c : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hpφ : Integrable (fun p : ℝ => (p : ℂ) * φ p)) :
    Continuous (fun tx : ℝ × ℝ => momentumCurrent c φ tx.1 tx.2) := by
  unfold momentumCurrent
  exact continuous_const.mul
    (Complex.continuous_im.comp ((continuous_wave c hφ).star.mul
      (continuous_wave c (integrable_momentumDerivative hpφ))))

lemma wave_at_origin (c : ℝ) (φ : ℝ → ℂ) : wave c φ 0 0 = ∫ p, φ p := by
  simp [wave, phase]

lemma momentumCurrent_at_origin (c : ℝ) (φ : ℝ → ℂ) :
    momentumCurrent c φ 0 0 = 2*c*(star (∫ p, φ p) * ((∫ p : ℝ, (p : ℂ)*φ p)*I)).im := by
  rw [momentumCurrent, wave_at_origin, wave_at_origin]
  have h : (∫ p, momentumDerivative φ p) = (∫ p : ℝ, (p : ℂ)*φ p)*I := by
    rw [← integral_mul_const]
    congr 1
    funext p
    unfold momentumDerivative
    ring
  rw [h]

/-- A moment criterion for negative current; the amplitude can have arbitrary support. -/
theorem momentumCurrent_at_origin_of_real_moments (c A B : ℝ) (φ : ℝ → ℂ)
    (hA : (∫ p, φ p) = (A : ℂ))
    (hB : (∫ p : ℝ, (p : ℂ)*φ p) = (B : ℂ)) :
    momentumCurrent c φ 0 0 = 2*c*A*B := by
  rw [momentumCurrent_at_origin, hA, hB]
  simp only [star_def, Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Opposite signs of the real zeroth and first moments force negative current. -/
theorem momentumCurrent_neg_of_real_moments {c A B : ℝ} (hc : 0 < c) (φ : ℝ → ℂ)
    (hA : (∫ p, φ p) = (A : ℂ))
    (hB : (∫ p : ℝ, (p : ℂ)*φ p) = (B : ℂ)) (hAB : A*B < 0) :
    momentumCurrent c φ 0 0 < 0 := by
  rw [momentumCurrent_at_origin_of_real_moments c A B φ hA hB]
  nlinarith [mul_neg_of_pos_of_neg (by positivity : 0 < 2*c) hAB]

/-- Strict negative current persists on an open interval of ordinary free evolution. -/
theorem momentumCurrent_neg_on_interval {c : ℝ} {φ : ℝ → ℂ} (hφ : Integrable φ)
    (hpφ : Integrable (fun p : ℝ => (p : ℂ)*φ p))
    {t x : ℝ} (hneg : momentumCurrent c φ t x < 0) :
    ∃ ε > 0, ∀ s : ℝ, |s-t| < ε → momentumCurrent c φ s x < 0 := by
  have hpair : Continuous (fun s : ℝ => (s, x)) :=
    continuous_id.prodMk continuous_const
  have hcont : Continuous (fun s : ℝ => momentumCurrent c φ s x) :=
    by
      simpa only [Function.comp_def] using
        (continuous_momentumCurrent c hφ hpφ).comp (f := fun s : ℝ => (s, x)) hpair
  have hevent : ∀ᶠ s in 𝓝 t, momentumCurrent c φ s x < 0 :=
    hcont.continuousAt.eventually (gt_mem_nhds hneg)
  rcases Metric.eventually_nhds_iff.mp hevent with ⟨ε, hε, h⟩
  refine ⟨ε, hε, fun s hs => h ?_⟩
  simpa [Real.dist_eq] using hs

end QuantumBackflow
