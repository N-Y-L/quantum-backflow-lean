import QuantumBackflow.MainTheorem

noncomputable section

namespace QuantumBackflow

/-- An explicit interference coefficient for any two separated positive bands. -/
def backflowCoefficient (a b d e : ℝ) : ℝ :=
  (b-a)*((a+b)+(d+e))/(2*(e-d)*(d+e))

/-- The chosen coefficient makes the zeroth and first spectral moments have opposite signs. -/
theorem backflowCoefficient_moments {a b d e : ℝ}
    (ha : 0 < a) (hab : a < b) (hbd : b < d) (hde : d < e) :
    0 < (b-a)-backflowCoefficient a b d e*(e-d) ∧
    (b^2-a^2)/2-backflowCoefficient a b d e*((e^2-d^2)/2) < 0 := by
  have hv : 0 < e-d := sub_pos.mpr hde
  have hs : 0 < d+e := by linarith
  have hg : 0 < (d+e)-(a+b) := by linarith
  have hz : (b-a)-backflowCoefficient a b d e*(e-d) =
      (b-a)*((d+e)-(a+b))/(2*(d+e)) := by
    unfold backflowCoefficient
    field_simp
    ring
  have hf : (b^2-a^2)/2-backflowCoefficient a b d e*((e^2-d^2)/2) =
      (b-a)*((a+b)-(d+e))/4 := by
    unfold backflowCoefficient
    field_simp
    ring
  rw [hz, hf]
  exact ⟨div_pos (mul_pos (sub_pos.mpr hab) hg) (by positivity),
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr hab) (by linarith))
      (by norm_num)⟩

/-- Every two separated positive bands have an explicit coefficient exhibiting backflow. -/
theorem chosenCoefficient_backflow {a b d e c : ℝ} (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hbd : b < d) (hde : d < e) :
    Backflow c (twoBand a b d e (backflowCoefficient a b d e)) 0 0 := by
  obtain ⟨hz, hf⟩ := backflowCoefficient_moments ha hab hbd hde
  exact twoBand_backflow hc ha hab hbd hde hz hf

/-- Existence on arbitrary separated positive intervals, without moment-sign hypotheses. -/
theorem arbitraryBands_backflow {a b d e c : ℝ} (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hbd : b < d) (hde : d < e) :
    ∃ r : ℝ, Backflow c (twoBand a b d e r) 0 0 :=
  ⟨backflowCoefficient a b d e, chosenCoefficient_backflow hc ha hab hbd hde⟩

/-- The construction works for arbitrary separated positive bands at every spacetime point. -/
theorem shifted_arbitraryBands_backflow {a b d e c : ℝ} (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hbd : b < d) (hde : d < e) (t₀ x₀ : ℝ) :
    ∃ r : ℝ,
      Backflow c (shiftedProfile c t₀ x₀ (twoBand a b d e r)) x₀ t₀ := by
  obtain ⟨hz, hf⟩ := backflowCoefficient_moments ha hab hbd hde
  exact ⟨backflowCoefficient a b d e,
    shifted_twoBand_backflow hc ha hab hbd hde hz hf t₀ x₀⟩

end QuantumBackflow
