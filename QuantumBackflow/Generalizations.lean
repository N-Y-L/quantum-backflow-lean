import QuantumBackflow.MainTheorem

open MeasureTheory Set Complex

noncomputable section
namespace QuantumBackflow

/-- Quantum backflow persists even when the whole momentum distribution is constrained above
an arbitrarily prescribed finite cutoff, at every chosen time and spatial boundary.
No lower bound on the amount of probability increase is asserted. -/
theorem quantum_backflow_above_cutoff {c : ℝ} (hc : 0 < c) (cutoff t₀ x₀ : ℝ) :
    ∃ φ : ℝ → ℂ, Backflow c φ x₀ t₀ ∧ ∀ p ≤ cutoff, φ p = 0 := by
  let a : ℝ := max 0 cutoff + 1
  let r : ℝ := (a+3/2)/(a+5/2)
  have ha : 0 < a := by dsimp [a]; linarith [le_max_left (0 : ℝ) cutoff]
  have hcut : cutoff < a := by dsimp [a]; linarith [le_max_right (0 : ℝ) cutoff]
  have hden : 0 < a+5/2 := by linarith
  have hr : r < 1 := by
    dsimp [r]
    exact (div_lt_one hden).mpr (by linarith)
  have hmul : r*(a+5/2) = a+3/2 := by
    dsimp [r]
    exact div_mul_cancel₀ _ hden.ne'
  have hzero : 0 < (a+1-a)-r*(a+3-(a+2)) := by nlinarith
  have hfirst : ((a+1)^2-a^2)/2-r*(((a+3)^2-(a+2)^2)/2) < 0 := by
    nlinarith
  refine ⟨shiftedProfile c t₀ x₀ (twoBand a (a+1) (a+2) (a+3) r),
    shifted_twoBand_backflow hc ha (by linarith) (by linarith) (by linarith)
      hzero hfirst t₀ x₀, ?_⟩
  intro p hp
  rw [shiftedProfile_eq_zero_iff]
  have hpa : p < a := lt_of_le_of_lt hp hcut
  simp only [twoBand, band_eq_zero_of_lt hpa,
    band_eq_zero_of_lt (by linarith : p < a+2), mul_zero, sub_zero]

/-- The cutoff statement also holds as an exact probability-one assertion at every time. -/
theorem quantum_backflow_with_probability_above_cutoff {c : ℝ} (hc : 0 < c)
    (cutoff t₀ x₀ : ℝ) :
    ∃ φ : ℝ → ℂ, Backflow c φ x₀ t₀ ∧
      ∀ t : ℝ, bornProbability (evolvedProfile c t φ) (Ioi cutoff) = 1 := by
  obtain ⟨φ, hb, hs⟩ := quantum_backflow_above_cutoff hc cutoff t₀ x₀
  refine ⟨φ, hb, fun t => ?_⟩
  rw [bornProbability_evolvedProfile]
  unfold bornProbability
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
    simp [hs p (not_lt.mp hp)]), div_self hb.momentum_mass_pos.ne']

end QuantumBackflow
