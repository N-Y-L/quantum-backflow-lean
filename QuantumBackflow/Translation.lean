import QuantumBackflow.FreeEvolution

open MeasureTheory Complex

noncomputable section

namespace QuantumBackflow

@[simp] lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma phase_add (u v : ℝ) : phase (u+v) = phase u * phase v := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] lemma phase_ne_zero (u : ℝ) : phase u ≠ 0 := Complex.exp_ne_zero _

/-- Exact current formula for arbitrary complex zeroth and first momentum moments. -/
theorem momentumCurrent_at_origin_complex_moments (c : ℝ) (φ : ℝ → ℂ) :
    momentumCurrent c φ 0 0 =
      2*c*(star (∫ p, φ p) * (∫ p : ℝ, (p : ℂ)*φ p)).re := by
  rw [momentumCurrent_at_origin]
  simp only [← mul_assoc, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero]

/-- The complex moment criterion is necessary and sufficient for negative current. -/
theorem momentumCurrent_neg_iff_complex_moments {c : ℝ} (hc : 0 < c) (φ : ℝ → ℂ) :
    momentumCurrent c φ 0 0 < 0 ↔
      (star (∫ p, φ p) * (∫ p : ℝ, (p : ℂ)*φ p)).re < 0 := by
  rw [momentumCurrent_at_origin_complex_moments]
  constructor
  · intro h
    by_contra hn
    have := mul_nonneg (by positivity : 0 ≤ 2*c) (le_of_not_gt hn)
    linarith
  · exact mul_neg_of_pos_of_neg (by positivity)

/-- A momentum phase moves the same free-particle experiment to a chosen time and position. -/
def shiftedProfile (c t₀ x₀ : ℝ) (φ : ℝ → ℂ) (p : ℝ) : ℂ :=
  phase (-p*x₀+c*p^2*t₀) * φ p

/-- Momentum measurement probabilities are unchanged by the translation phase. -/
@[simp] theorem norm_shiftedProfile (c t₀ x₀ : ℝ) (φ : ℝ → ℂ) (p : ℝ) :
    ‖shiftedProfile c t₀ x₀ φ p‖ = ‖φ p‖ := by
  simp [shiftedProfile]

@[simp] theorem normSq_shiftedProfile (c t₀ x₀ : ℝ) (φ : ℝ → ℂ) (p : ℝ) :
    Complex.normSq (shiftedProfile c t₀ x₀ φ p) = Complex.normSq (φ p) := by
  simp only [Complex.normSq_eq_norm_sq, norm_shiftedProfile]

/-- In particular the momentum support is exactly preserved. -/
@[simp] theorem shiftedProfile_eq_zero_iff (c t₀ x₀ : ℝ) (φ : ℝ → ℂ) (p : ℝ) :
    shiftedProfile c t₀ x₀ φ p = 0 ↔ φ p = 0 := by
  simp [shiftedProfile]

@[simp] theorem support_shiftedProfile (c t₀ x₀ : ℝ) (φ : ℝ → ℂ) :
    Function.support (shiftedProfile c t₀ x₀ φ) = Function.support φ := by
  ext p
  simp [Function.mem_support]

lemma integrable_shiftedProfile (c t₀ x₀ : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) :
    Integrable (shiftedProfile c t₀ x₀ φ) := by
  exact integrable_phase_mul hφ (by fun_prop)

/-- Every integrable polynomial momentum moment remains integrable. -/
lemma integrable_moment_shiftedProfile (c t₀ x₀ : ℝ) {φ : ℝ → ℂ} (n : ℕ)
    (hφ : Integrable (fun p : ℝ => (p : ℂ)^n * φ p)) :
    Integrable (fun p : ℝ => (p : ℂ)^n * shiftedProfile c t₀ x₀ φ p) := by
  convert integrable_phase_mul hφ (θ := fun p : ℝ => -p*x₀+c*p^2*t₀) (by fun_prop) using 1
  funext p
  simp only [shiftedProfile]
  ring

/-- The translated spectral phase has exactly the expected free evolution. -/
theorem wave_shiftedProfile (c t₀ x₀ t x : ℝ) (φ : ℝ → ℂ) :
    wave c (shiftedProfile c t₀ x₀ φ) t x = wave c φ (t-t₀) (x-x₀) := by
  unfold wave shiftedProfile
  congr 1
  funext p
  rw [← mul_assoc, ← phase_add]
  congr 2
  ring

lemma momentumDerivative_shiftedProfile (c t₀ x₀ : ℝ) (φ : ℝ → ℂ) :
    momentumDerivative (shiftedProfile c t₀ x₀ φ) =
      shiftedProfile c t₀ x₀ (momentumDerivative φ) := by
  funext p
  simp only [momentumDerivative, shiftedProfile]
  ring

/-- Current translates with the wave, while the entire momentum distribution is unchanged. -/
theorem momentumCurrent_shiftedProfile (c t₀ x₀ t x : ℝ) (φ : ℝ → ℂ) :
    momentumCurrent c (shiftedProfile c t₀ x₀ φ) t x =
      momentumCurrent c φ (t-t₀) (x-x₀) := by
  simp only [momentumCurrent, momentumDerivative_shiftedProfile, wave_shiftedProfile]

/-- Any real-moment witness can be placed at any prescribed time and spatial boundary. -/
theorem shifted_momentumCurrent_neg_of_real_moments {c A B : ℝ} (hc : 0 < c)
    (φ : ℝ → ℂ) (hA : (∫ p, φ p) = (A : ℂ))
    (hB : (∫ p : ℝ, (p : ℂ)*φ p) = (B : ℂ)) (hAB : A*B < 0) (t₀ x₀ : ℝ) :
    momentumCurrent c (shiftedProfile c t₀ x₀ φ) t₀ x₀ < 0 := by
  simpa only [momentumCurrent_shiftedProfile, sub_self] using
    momentumCurrent_neg_of_real_moments hc φ hA hB hAB

end QuantumBackflow
