import QuantumBackflow.FreeEvolution
import QuantumBackflow.Packets
import QuantumBackflow.Translation

open MeasureTheory Set Complex
open scoped Topology
noncomputable section
namespace QuantumBackflow

lemma wave_band_interval {a b : ℝ} (hab : a ≤ b) (c t x : ℝ) :
    wave c (band a b) t x = ∫ p in a..b, phase (p*x-c*p^2*t) := by
  unfold wave
  have he : (fun p => phase (p*x-c*p^2*t)*band a b p) =
      (Icc a b).indicator (fun p => phase (p*x-c*p^2*t)) := by
    ext p
    by_cases hp : p ∈ Icc a b <;> simp [band, hp]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

lemma wave_weighted_band_interval {a b : ℝ} (hab : a ≤ b) (c t x : ℝ) (n : ℕ) :
    wave c (fun p : ℝ => (p:ℂ)^n*band a b p) t x =
      ∫ p in a..b, (p:ℂ)^n*phase (p*x-c*p^2*t) := by
  unfold wave
  have he : (fun p : ℝ => phase (p*x-c*p^2*t)*((p:ℂ)^n*band a b p)) =
      (Icc a b).indicator (fun p : ℝ => (p:ℂ)^n*phase (p*x-c*p^2*t)) := by
    ext p
    by_cases hp : p ∈ Icc a b <;> simp [band, hp, mul_comm]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

lemma wave_sub (c : ℝ) {φ χ : ℝ → ℂ} (hφ : Integrable φ) (hχ : Integrable χ)
    (t x : ℝ) : wave c (fun p => φ p - χ p) t x = wave c φ t x - wave c χ t x := by
  unfold wave
  simp_rw [mul_sub]
  exact integral_sub (integrable_phase_mul hφ (by fun_prop))
    (integrable_phase_mul hχ (by fun_prop))

lemma wave_weighted_twoBand (a b d e r c t x : ℝ) (n : ℕ) :
    wave c (fun p : ℝ => (p:ℂ)^n*twoBand a b d e r p) t x =
      wave c (fun p : ℝ => (p:ℂ)^n*band a b p) t x -
        (r:ℂ)*wave c (fun p : ℝ => (p:ℂ)^n*band d e p) t x := by
  have he : (fun p : ℝ => (p:ℂ)^n*twoBand a b d e r p) =
      (fun p : ℝ => (p:ℂ)^n*band a b p - (r:ℂ)*((p:ℂ)^n*band d e p)) := by
    ext p; unfold twoBand; ring
  rw [he, wave_sub c (integrable_weighted_band a b n)
    ((integrable_weighted_band d e n).const_mul _), wave_const_mul]

lemma twoBand_current_origin {a b d e r : ℝ} (hab : a ≤ b) (hde : d ≤ e) (c : ℝ) :
    momentumCurrent c (twoBand a b d e r) 0 0 =
      2*c*((b-a)-r*(e-d))*((b^2-a^2)/2-r*((e^2-d^2)/2)) := by
  exact momentumCurrent_at_origin_of_real_moments c _ _ (twoBand a b d e r)
    (integral_twoBand hab hde) (integral_first_twoBand hab hde)

/-- Two separated positive bands exhibit backflow when their first moments oppose their amplitudes. -/
lemma twoBand_current_negative {a b d e r c : ℝ} (hc : 0 < c)
    (hab : a ≤ b) (hde : d ≤ e)
    (hzero : 0 < (b-a)-r*(e-d))
    (hfirst : (b^2-a^2)/2-r*((e^2-d^2)/2) < 0) :
    momentumCurrent c (twoBand a b d e r) 0 0 < 0 := by
  rw [twoBand_current_origin hab hde]
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hc) hzero) hfirst

lemma exampleProfile_current_origin (c : ℝ) : momentumCurrent c exampleProfile 0 0 = -c := by
  rw [momentumCurrent_at_origin c exampleProfile,
    exampleProfile_integral, exampleProfile_first_integral]
  simp [Complex.mul_im]
  ring

/-- Free time evolution changes only the momentum phase. -/
def evolvedProfile (c t : ℝ) (φ : ℝ → ℂ) (p : ℝ) : ℂ := phase (-c*p^2*t)*φ p

lemma normSq_evolvedProfile (c t : ℝ) (φ : ℝ → ℂ) (p : ℝ) :
    normSq (evolvedProfile c t φ p) = normSq (φ p) := by
  simp [evolvedProfile, Complex.normSq_eq_norm_sq]

lemma bornProbability_evolvedProfile (c t : ℝ) (φ : ℝ → ℂ) (s : Set ℝ) :
    bornProbability (evolvedProfile c t φ) s = bornProbability φ s := by
  simp only [bornProbability, normSq_evolvedProfile]

/-- The position wave and the phase-evolved spectrum are a Fourier pair at every time. -/
lemma wave_from_evolvedProfile (c t x : ℝ) (φ : ℝ → ℂ) :
    wave c φ t x = ∫ p, phase (p*x)*evolvedProfile c t φ p := by
  unfold wave evolvedProfile
  congr 1
  funext p
  rw [← mul_assoc, ← phase_add]
  congr 2
  ring

end QuantumBackflow
