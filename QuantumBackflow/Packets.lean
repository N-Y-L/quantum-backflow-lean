import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Compact positive-momentum profiles and their moments. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace QuantumBackflow

/-- Constant amplitude on a finite momentum interval. -/
def band (a b : ℝ) (p : ℝ) : ℂ := (Icc a b).indicator (fun _ => 1) p

/-- Two disjoint bands, with destructive interference between them. -/
def twoBand (a b d e r : ℝ) (p : ℝ) : ℂ := band a b p - (r : ℂ) * band d e p

/-- Born probability; the nonzero wave function need not be normalized in advance. -/
def bornProbability (f : ℝ → ℂ) (s : Set ℝ) : ℝ :=
  (∫ x in s, Complex.normSq (f x)) / ∫ x, Complex.normSq (f x)

lemma band_eq_zero_of_lt {a b p : ℝ} (h : p < a) : band a b p = 0 := by
  simp [band, not_le.mpr h]

lemma twoBand_positive_support {a b d e r : ℝ} (ha : 0 < a) (hd : 0 < d)
    {p : ℝ} (hp : p ≤ 0) : twoBand a b d e r p = 0 := by
  simp [twoBand, band_eq_zero_of_lt (lt_of_le_of_lt hp ha),
    band_eq_zero_of_lt (lt_of_le_of_lt hp hd)]

lemma integrable_band (a b : ℝ) : Integrable (band a b) := by
  exact ((continuous_const : Continuous (fun _ : ℝ => (1 : ℂ))).integrableOn_Icc).integrable_indicator measurableSet_Icc

lemma integrable_twoBand (a b d e r : ℝ) : Integrable (twoBand a b d e r) :=
  (integrable_band a b).sub ((integrable_band d e).const_mul _)

lemma integral_band {a b : ℝ} (hab : a ≤ b) : ∫ p, band a b p = (b - a : ℝ) := by
  simp [band, integral_indicator measurableSet_Icc, integral_const,
    max_eq_left (sub_nonneg.mpr hab)]

lemma integral_twoBand {a b d e r : ℝ} (hab : a ≤ b) (hde : d ≤ e) :
    ∫ p, twoBand a b d e r p = ((b - a) - r * (e - d) : ℝ) := by
  change (∫ p, band a b p - (r : ℂ) * band d e p) = _
  rw [integral_sub (integrable_band a b) ((integrable_band d e).const_mul _),
    integral_const_mul, integral_band hab, integral_band hde]
  push_cast
  rfl

lemma weighted_band (a b : ℝ) (n : ℕ) :
    (fun p : ℝ => (p : ℂ)^n * band a b p) =
      (Icc a b).indicator (fun p : ℝ => (p : ℂ)^n) := by
  ext p
  by_cases hp : p ∈ Icc a b <;> simp [band, hp]

lemma integrable_weighted_band (a b : ℝ) (n : ℕ) :
    Integrable (fun p : ℝ => (p : ℂ)^n * band a b p) := by
  rw [weighted_band]
  exact ((Complex.continuous_ofReal.pow n).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

lemma integrable_weighted_twoBand (a b d e r : ℝ) (n : ℕ) :
    Integrable (fun p : ℝ => (p : ℂ)^n * twoBand a b d e r p) := by
  have h := (integrable_weighted_band a b n).sub
    ((integrable_weighted_band d e n).const_mul (r : ℂ))
  convert h using 1
  ext p
  change (p : ℂ)^n * (band a b p - (r : ℂ)*band d e p) =
    (p : ℂ)^n*band a b p - (r : ℂ)*((p : ℂ)^n*band d e p)
  ring

lemma integral_first_band {a b : ℝ} (hab : a ≤ b) :
    ∫ p : ℝ, (p : ℂ) * band a b p = ((b^2-a^2)/2 : ℝ) := by
  have he : (fun p : ℝ => (p : ℂ)*band a b p) =
      (Icc a b).indicator (fun p : ℝ => (p : ℂ)) := by
    simpa using weighted_band a b 1
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_ofReal, integral_id]

lemma integral_first_twoBand {a b d e r : ℝ} (hab : a ≤ b) (hde : d ≤ e) :
    ∫ p : ℝ, (p : ℂ) * twoBand a b d e r p =
      ((b^2-a^2)/2 - r*((e^2-d^2)/2) : ℝ) := by
  have hf : (fun p : ℝ => (p : ℂ)*twoBand a b d e r p) =
      (fun p : ℝ => (p : ℂ)*band a b p - (r : ℂ)*((p : ℂ)*band d e p)) := by
    ext p; simp only [twoBand]; ring
  rw [hf, integral_sub (by simpa using integrable_weighted_band a b 1)
    (by simpa using (integrable_weighted_band d e 1).const_mul (r : ℂ)),
    integral_const_mul, integral_first_band hab, integral_first_band hde]
  push_cast
  rfl

/-- An explicit compactly supported backflow profile. -/
def exampleProfile : ℝ → ℂ := fun p => 2 * band 1 2 p - band 3 4 p

lemma exampleProfile_eq : exampleProfile = fun p => 2 * twoBand 1 2 3 4 (1/2) p := by
  ext p
  simp only [exampleProfile, twoBand]
  push_cast
  ring

lemma exampleProfile_integral : ∫ p, exampleProfile p = 1 := by
  rw [exampleProfile_eq, integral_const_mul, integral_twoBand (by norm_num) (by norm_num)]
  norm_num

lemma exampleProfile_first_integral : ∫ p : ℝ, (p : ℂ)*exampleProfile p = -(1/2 : ℂ) := by
  have h : (fun p : ℝ => (p : ℂ)*exampleProfile p) =
      (fun p : ℝ => 2*((p : ℂ)*twoBand 1 2 3 4 (1/2) p)) := by
    rw [exampleProfile_eq]; funext p; ring
  rw [h, integral_const_mul, integral_first_twoBand (by norm_num) (by norm_num)]
  norm_num

lemma integrable_normSq_twoBand {a b d e r : ℝ} (hbd : b < d) :
    Integrable (fun p => Complex.normSq (twoBand a b d e r p)) := by
  have he : (fun p => Complex.normSq (twoBand a b d e r p)) =
      (fun p => (Icc a b).indicator (fun _ => (1:ℝ)) p +
        r^2 * (Icc d e).indicator (fun _ => (1:ℝ)) p) := by
    funext p
    by_cases hab : p ∈ Icc a b
    · have hde : p ∉ Icc d e := by intro hp; linarith [hab.2, hp.1]
      simp [twoBand, band, hab, hde]
    · by_cases hde : p ∈ Icc d e <;> simp [twoBand, band, hab, hde, Complex.normSq_ofReal, sq]
  rw [he]
  have hi (u v : ℝ) : Integrable ((Icc u v).indicator (fun _ => (1:ℝ))) :=
    ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).integrable_indicator
      measurableSet_Icc
  exact (hi a b).add ((hi d e).const_mul _)

lemma integral_normSq_twoBand {a b d e r : ℝ} (hab : a ≤ b) (hde : d ≤ e)
    (hbd : b < d) :
    ∫ p, Complex.normSq (twoBand a b d e r p) = (b-a)+r^2*(e-d) := by
  have he : (fun p => Complex.normSq (twoBand a b d e r p)) =
      (fun p => (Icc a b).indicator (fun _ => (1:ℝ)) p +
        r^2 * (Icc d e).indicator (fun _ => (1:ℝ)) p) := by
    funext p
    by_cases ha : p ∈ Icc a b
    · have hd : p ∉ Icc d e := by intro hp; linarith [ha.2, hp.1]
      simp [twoBand, band, ha, hd]
    · by_cases hd : p ∈ Icc d e <;> simp [twoBand, band, ha, hd, Complex.normSq_ofReal, sq]
  have hi (u v : ℝ) : Integrable ((Icc u v).indicator (fun _ => (1:ℝ))) :=
    ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).integrable_indicator
      measurableSet_Icc
  rw [he, integral_add (hi a b) ((hi d e).const_mul _), integral_const_mul]
  simp [integral_indicator measurableSet_Icc, max_eq_left (sub_nonneg.mpr hab),
    max_eq_left (sub_nonneg.mpr hde)]

lemma bornProbability_positive_eq_one {f : ℝ → ℂ}
    (hs : ∀ p ≤ 0, f p = 0) (hm : (∫ p, Complex.normSq (f p)) ≠ 0) :
    bornProbability f (Ioi 0) = 1 := by
  unfold bornProbability
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
    simp [hs p (not_lt.mp hp)]), div_self hm]

lemma twoBand_momentum_probability {a b d e r : ℝ} (ha : 0 < a) (hab : a < b)
    (hbd : b < d) (hde : d ≤ e) :
    bornProbability (twoBand a b d e r) (Ioi 0) = 1 := by
  apply bornProbability_positive_eq_one
  · exact fun p hp => twoBand_positive_support ha (lt_trans (lt_trans ha hab) hbd) hp
  · rw [integral_normSq_twoBand hab.le hde hbd]
    have : 0 ≤ r^2*(e-d) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hde)
    linarith

lemma exampleProfile_integrable_moment (n : ℕ) :
    Integrable (fun p : ℝ => (p:ℂ)^n*exampleProfile p) := by
  have h := (integrable_weighted_twoBand 1 2 3 4 (1/2) n).const_mul (2:ℂ)
  convert h using 1
  funext p
  rw [exampleProfile_eq]
  ring

lemma exampleProfile_mass : ∫ p, Complex.normSq (exampleProfile p) = 5 := by
  have he : (fun p => Complex.normSq (exampleProfile p)) =
      (fun p => 4*Complex.normSq (twoBand 1 2 3 4 (1/2) p)) := by
    funext p
    rw [exampleProfile_eq]
    norm_num [Complex.normSq_mul]
  rw [he, integral_const_mul,
    integral_normSq_twoBand (by norm_num) (by norm_num) (by norm_num)]
  norm_num

lemma exampleProfile_momentum_probability : bornProbability exampleProfile (Ioi 0) = 1 := by
  apply bornProbability_positive_eq_one
  · intro p hp
    rw [exampleProfile_eq]
    simp [twoBand_positive_support (show (0:ℝ)<1 by norm_num)
      (show (0:ℝ)<3 by norm_num) hp]
  · rw [exampleProfile_mass]
    norm_num

end QuantumBackflow
