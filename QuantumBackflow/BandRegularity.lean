import QuantumBackflow.BandEvolution
import QuantumBackflow.FourierDecay
import QuantumBackflow.DecayRegularity

open MeasureTheory Complex Set
open scoped Topology
noncomputable section
namespace QuantumBackflow

/-- All polynomial moments of two finite bands have uniform spatial decay. -/
lemma exists_twoBand_moment_bound (c r T : ℝ) (n : ℕ) {a b d e : ℝ}
    (hab : a ≤ b) (hde : d ≤ e) :
    ∃ K > 0, ∀ t, |t| ≤ T → ∀ x,
      ‖wave c (fun p : ℝ => (p:ℂ)^n*twoBand a b d e r p) t x‖ ≤ K ∧
      |x| *‖wave c (fun p : ℝ => (p:ℂ)^n*twoBand a b d e r p) t x‖ ≤ K := by
  obtain ⟨B₁,D₁,hB₁,hD₁,h₁⟩ := exists_bandMoment_bounds c n hab T
  obtain ⟨B₂,D₂,hB₂,hD₂,h₂⟩ := exists_bandMoment_bounds c n hde T
  refine ⟨B₁+D₁+|r| *(B₂+D₂)+1, by positivity, ?_⟩
  intro t ht x
  rw [wave_weighted_twoBand, wave_weighted_band_interval hab,
    wave_weighted_band_interval hde]
  change ‖bandMoment c n a b t x - (r:ℂ)*bandMoment c n d e t x‖ ≤ _ ∧
    |x| *‖bandMoment c n a b t x - (r:ℂ)*bandMoment c n d e t x‖ ≤ _
  have hnorm : ‖bandMoment c n a b t x - (r:ℂ)*bandMoment c n d e t x‖ ≤
      ‖bandMoment c n a b t x‖ + |r| *‖bandMoment c n d e t x‖ := by
    simpa using norm_sub_le (bandMoment c n a b t x) ((r:ℂ)*bandMoment c n d e t x)
  have hplain := hnorm.trans (add_le_add (h₁ t ht x).1
    (mul_le_mul_of_nonneg_left (h₂ t ht x).1 (abs_nonneg r)))
  have hweighted := mul_le_mul_of_nonneg_left hnorm (abs_nonneg x)
  have hlower := mul_le_mul_of_nonneg_left (h₂ t ht x).2 (abs_nonneg r)
  have hz : 0 ≤ |r| := abs_nonneg r
  constructor
  · nlinarith
  · nlinarith [(h₁ t ht x).2]

lemma wave_momentumDerivative_eq (c : ℝ) (φ : ℝ → ℂ) (t x : ℝ) :
    wave c (momentumDerivative φ) t x = I * wave c (fun p : ℝ => (p:ℂ)*φ p) t x := by
  have he : momentumDerivative φ = fun p : ℝ => I*((p:ℂ)*φ p) := by
    ext p; unfold momentumDerivative; ring
  rw [he, wave_const_mul]

lemma norm_wave_momentumDerivative (c : ℝ) (φ : ℝ → ℂ) (t x : ℝ) :
    ‖wave c (momentumDerivative φ) t x‖ =
      ‖wave c (fun p : ℝ => (p:ℂ)^1*φ p) t x‖ := by
  rw [wave_momentumDerivative_eq]
  simp

lemma norm_wave_momentumDerivative_twice (c : ℝ) (φ : ℝ → ℂ) (t x : ℝ) :
    ‖wave c (momentumDerivative (momentumDerivative φ)) t x‖ =
      ‖wave c (fun p : ℝ => (p:ℂ)^2*φ p) t x‖ := by
  rw [momentumDerivative_twice]
  have he : (fun p : ℝ => -((p:ℂ)^2*φ p)) =
      (fun p : ℝ => (-1:ℂ)*((p:ℂ)^2*φ p)) := by ext p; ring
  rw [he, wave_const_mul]
  simp

lemma uniformDecay_twoBand (c r : ℝ) {a b d e : ℝ} (hab : a ≤ b) (hde : d ≤ e) :
    UniformWaveDecay (wave c (twoBand a b d e r))
      (wave c (momentumDerivative (twoBand a b d e r)))
      (wave c (momentumDerivative (momentumDerivative (twoBand a b d e r)))) := by
  intro T _
  obtain ⟨K₀,hK₀,h₀⟩ := exists_twoBand_moment_bound c r T 0 hab hde
  obtain ⟨K₁,hK₁,h₁⟩ := exists_twoBand_moment_bound c r T 1 hab hde
  obtain ⟨K₂,hK₂,h₂⟩ := exists_twoBand_moment_bound c r T 2 hab hde
  refine ⟨K₀+K₁+K₂, by positivity, ?_⟩
  intro t ht x
  have hz := h₀ t ht x
  have ho := h₁ t ht x
  have ht' := h₂ t ht x
  simp only [pow_zero, one_mul] at hz
  rw [norm_wave_momentumDerivative, norm_wave_momentumDerivative_twice]
  exact ⟨⟨hz.1.trans (by linarith), hz.2.trans (by linarith)⟩,
    ⟨ho.1.trans (by linarith), ho.2.trans (by linarith)⟩,
    ⟨ht'.1.trans (by linarith), ht'.2.trans (by linarith)⟩⟩

/-- The actual free evolution of every finite two-band profile satisfies all flux hypotheses. -/
theorem regular_twoBand (c r : ℝ) {a b d e : ℝ} (hab : a ≤ b) (hde : d ≤ e) :
    SchrodingerRegular c (wave c (twoBand a b d e r))
      (wave c (momentumDerivative (twoBand a b d e r)))
      (wave c (momentumDerivative (momentumDerivative (twoBand a b d e r)))) := by
  have h₀ := integrable_twoBand a b d e r
  have h₁ : Integrable (fun p : ℝ => (p:ℂ)*twoBand a b d e r p) := by
    simpa using integrable_weighted_twoBand a b d e r 1
  have h₂ := integrable_weighted_twoBand a b d e r 2
  have hd := integrable_momentumDerivative h₁
  have hdd : Integrable (momentumDerivative (momentumDerivative (twoBand a b d e r))) := by
    rw [momentumDerivative_twice]
    exact h₂.neg
  exact {
    continuous_wave := continuous_wave c h₀
    continuous_first := continuous_wave c hd
    continuous_second := continuous_wave c hdd
    schrodinger := schrodinger_time c h₀ h₂
    spatial_derivative := hasDerivAt_wave_space c h₀ h₁
    spatial_second_derivative := hasDerivAt_wave_space_derivative c h₁ h₂
    uniform_decay := uniformDecay_twoBand c r hab hde }

end QuantumBackflow
