import QuantumBackflow.Translation
import QuantumBackflow.DecayRegularity

open MeasureTheory Set
open scoped Topology

noncomputable section
namespace QuantumBackflow

/-- Translation in both independent variables. -/
def spacetimeShift (t₀ x₀ : ℝ) (ψ : ℝ → ℝ → ℂ) (t x : ℝ) : ℂ :=
  ψ (t-t₀) (x-x₀)

private lemma continuous_spacetimeShift {ψ : ℝ → ℝ → ℂ}
    (hψ : Continuous (Function.uncurry ψ)) (t₀ x₀ : ℝ) :
    Continuous (Function.uncurry (spacetimeShift t₀ x₀ ψ)) := by
  have hpair : Continuous (fun tx : ℝ × ℝ => (tx.1-t₀, tx.2-x₀)) := by fun_prop
  simpa only [Function.comp_def, Function.uncurry_def, spacetimeShift] using
    hψ.comp (f := fun tx : ℝ × ℝ => (tx.1-t₀, tx.2-x₀)) hpair

private lemma translated_decay_bound {K x₀ x : ℝ} {z : ℂ} (hK : 0 ≤ K)
    (hz : ‖z‖ ≤ K) (hxz : |x-x₀| *‖z‖ ≤ K) :
    ‖z‖ ≤ K*(1+|x₀|) ∧ |x| *‖z‖ ≤ K*(1+|x₀|) := by
  have habs : |x| ≤ |x-x₀|+|x₀| := by
    simpa only [sub_add_cancel] using abs_add_le (x-x₀) x₀
  have hprod := mul_le_mul_of_nonneg_right habs (norm_nonneg z)
  have hprod' := mul_le_mul_of_nonneg_left hz (abs_nonneg x₀)
  constructor <;> nlinarith [mul_nonneg hK (abs_nonneg x₀)]

/-- The elementary decay hypothesis is invariant under any finite spacetime translation. -/
theorem UniformWaveDecay.shift {ψ ψx ψxx : ℝ → ℝ → ℂ}
    (h : UniformWaveDecay ψ ψx ψxx) (t₀ x₀ : ℝ) :
    UniformWaveDecay (spacetimeShift t₀ x₀ ψ) (spacetimeShift t₀ x₀ ψx)
      (spacetimeShift t₀ x₀ ψxx) := by
  intro T hT
  obtain ⟨K, hK, hb⟩ := h (T+|t₀|) (by positivity)
  refine ⟨K*(1+|x₀|), by positivity, ?_⟩
  intro t ht x
  have htt : |t-t₀| ≤ T+|t₀| :=
    (abs_sub t t₀).trans (by linarith)
  have hbx := hb (t-t₀) htt (x-x₀)
  exact ⟨translated_decay_bound hK hbx.1.1 hbx.1.2,
    translated_decay_bound hK hbx.2.1.1 hbx.2.1.2,
    translated_decay_bound hK hbx.2.2.1 hbx.2.2.2⟩

/-- Classical Schrödinger regularity, including all decay estimates, survives translation. -/
theorem SchrodingerRegular.shift {c : ℝ} {ψ ψx ψxx : ℝ → ℝ → ℂ}
    (h : SchrodingerRegular c ψ ψx ψxx) (t₀ x₀ : ℝ) :
    SchrodingerRegular c (spacetimeShift t₀ x₀ ψ) (spacetimeShift t₀ x₀ ψx)
      (spacetimeShift t₀ x₀ ψxx) := by
  refine ⟨continuous_spacetimeShift h.continuous_wave t₀ x₀,
    continuous_spacetimeShift h.continuous_first t₀ x₀,
    continuous_spacetimeShift h.continuous_second t₀ x₀, ?_, ?_, ?_, h.uniform_decay.shift t₀ x₀⟩
  · intro t x
    simpa only [spacetimeShift, Function.comp_def, one_smul] using
      (h.schrodinger (t-t₀) (x-x₀)).scomp t ((hasDerivAt_id t).sub_const t₀)
  · intro t x
    simpa only [spacetimeShift, Function.comp_def, one_smul] using
      (h.spatial_derivative (t-t₀) (x-x₀)).scomp x ((hasDerivAt_id x).sub_const x₀)
  · intro t x
    simpa only [spacetimeShift, Function.comp_def, one_smul] using
      (h.spatial_second_derivative (t-t₀) (x-x₀)).scomp x ((hasDerivAt_id x).sub_const x₀)

/-- The translated spectral amplitude remains an ordinary free Schrödinger solution. -/
theorem SchrodingerRegular.of_shiftedProfile {c : ℝ} {φ : ℝ → ℂ}
    (h : SchrodingerRegular c (wave c φ) (wave c (momentumDerivative φ))
      (wave c (momentumDerivative (momentumDerivative φ)))) (t₀ x₀ : ℝ) :
    SchrodingerRegular c (wave c (shiftedProfile c t₀ x₀ φ))
      (wave c (momentumDerivative (shiftedProfile c t₀ x₀ φ)))
      (wave c (momentumDerivative (momentumDerivative (shiftedProfile c t₀ x₀ φ)))) := by
  have hw (χ : ℝ → ℂ) : wave c (shiftedProfile c t₀ x₀ χ) = spacetimeShift t₀ x₀ (wave c χ) := by
    funext t x
    exact wave_shiftedProfile c t₀ x₀ t x χ
  simpa only [momentumDerivative_shiftedProfile, hw] using h.shift t₀ x₀

end QuantumBackflow
