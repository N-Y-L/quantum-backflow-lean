import QuantumBackflow.BandRegularity
import QuantumBackflow.ShiftRegularity

open MeasureTheory Set Complex
open scoped Topology
noncomputable section
namespace QuantumBackflow

/-- A finite, nonzero Fourier-related state with positive momentum, ordinary free evolution,
and a full interval of increasing left-half-line Born probability. -/
structure Backflow (c : ℝ) (φ : ℝ → ℂ) (a t₀ : ℝ) : Prop where
  momentum_integrable : Integrable (fun p => normSq (φ p))
  momentum_mass_pos : 0 < ∫ p, normSq (φ p)
  positive_momentum : ∀ t, bornProbability (evolvedProfile c t φ) (Ioi 0) = 1
  position_integrable : ∀ t, Integrable (density (wave c φ) t)
  position_mass_pos : ∀ t, 0 < totalMass (wave c φ) t
  mass_conserved : ∀ t s, totalMass (wave c φ) t = totalMass (wave c φ) s
  schrodinger : ∀ t x, I * deriv (fun s => wave c φ s x) t =
    -(c:ℂ) * deriv (deriv (wave c φ t)) x
  probability_bounds : ∀ t, leftProbability (wave c φ) a t ∈ Icc 0 1
  probability_increases : ∃ δ > 0,
    (∀ t ∈ Ioo (t₀-δ) (t₀+δ), 0 < deriv (leftProbability (wave c φ) a) t) ∧
    StrictMonoOn (leftProbability (wave c φ) a) (Ioo (t₀-δ) (t₀+δ))

/-- A general criterion for any positive-momentum Fourier amplitude satisfying the explicit
regularity and decay conditions. Finite-band instances discharge these conditions below. -/
theorem backflow_of_regular {c a t₀ : ℝ} {φ : ℝ → ℂ}
    (hreg : SchrodingerRegular c (wave c φ) (wave c (momentumDerivative φ))
      (wave c (momentumDerivative (momentumDerivative φ))))
    (h₀ : Integrable φ) (h₁ : Integrable (fun p : ℝ => (p:ℂ)*φ p))
    (h₂ : Integrable (fun p : ℝ => (p:ℂ)^2*φ p))
    (hp : Integrable (fun p => normSq (φ p))) (hp0 : 0 < ∫ p, normSq (φ p))
    (hs : ∀ p ≤ 0, φ p = 0) (hj : momentumCurrent c φ t₀ a < 0) :
    Backflow c φ a t₀ := by
  have hne : wave c φ t₀ a ≠ 0 := by
    intro he
    simp [momentumCurrent, he] at hj
  have hm (t : ℝ) := hreg.totalMass_pos hne t
  exact {
    momentum_integrable := hp
    momentum_mass_pos := hp0
    positive_momentum := fun t => by
      rw [bornProbability_evolvedProfile]
      exact bornProbability_positive_eq_one hs hp0.ne'
    position_integrable := fun t => (hreg.fluxRegularAt t).density_integrable
    position_mass_pos := hm
    mass_conserved := hreg.totalMass_eq
    schrodinger := free_schrodinger c h₀ h₁ h₂
    probability_bounds := fun t => leftProbability_mem_Icc
      (hreg.fluxRegularAt t).density_integrable (hm t)
    probability_increases := hreg.backflow_of_current_neg hj }

/-- Generalized finite-band backflow: neither band widths nor coefficient are fixed. -/
theorem twoBand_backflow {a b d e r c : ℝ} (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hbd : b < d) (hde : d < e)
    (hzero : 0 < (b-a)-r*(e-d))
    (hfirst : (b^2-a^2)/2-r*((e^2-d^2)/2) < 0) :
    Backflow c (twoBand a b d e r) 0 0 := by
  let φ := twoBand a b d e r
  have hreg := regular_twoBand c r hab.le hde.le
  have hne : wave c φ 0 0 ≠ 0 := by
    rw [wave_at_origin, integral_twoBand hab.le hde.le]
    exact_mod_cast hzero.ne'
  have hm (t : ℝ) : 0 < totalMass (wave c φ) t := hreg.totalMass_pos hne t
  have hj : current c (wave c φ) (wave c (momentumDerivative φ)) 0 0 < 0 :=
    twoBand_current_negative hc hab.le hde.le hzero hfirst
  refine {
    momentum_integrable := integrable_normSq_twoBand hbd
    momentum_mass_pos := ?_
    positive_momentum := ?_
    position_integrable := fun t => (hreg.fluxRegularAt t).density_integrable
    position_mass_pos := hm
    mass_conserved := hreg.totalMass_eq
    schrodinger := free_schrodinger c (integrable_twoBand a b d e r)
      (by simpa using integrable_weighted_twoBand a b d e r 1)
      (integrable_weighted_twoBand a b d e r 2)
    probability_bounds := fun t => leftProbability_mem_Icc
      (hreg.fluxRegularAt t).density_integrable (hm t)
    probability_increases := hreg.backflow_open_interval (hm 0) hj }
  · rw [integral_normSq_twoBand hab.le hde.le hbd]
    have hh : 0 ≤ r^2*(e-d) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hde.le)
    linarith
  · intro t
    rw [bornProbability_evolvedProfile]
    exact twoBand_momentum_probability ha hab hbd hde.le

/-- A concrete continuum witness for every positive Schrödinger coefficient. -/
theorem explicit_quantum_backflow {c : ℝ} (hc : 0 < c) :
    Backflow c (twoBand 1 2 3 4 (1/2)) 0 0 :=
  twoBand_backflow hc (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- In physical units, the construction works for every positive mass and Planck parameter.
The integration variable is wave number; physical momentum is `ℏ` times that variable. -/
theorem quantum_backflow_physical {ℏ m : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m) :
    Backflow (ℏ/(2*m)) (twoBand 1 2 3 4 (1/2)) 0 0 :=
  explicit_quantum_backflow (div_pos hℏ (mul_pos (by norm_num) hm))

/-- Equal-width bands admit a simple interval of coefficients giving backflow. -/
theorem equalWidth_backflow {a d w r c : ℝ} (hc : 0 < c)
    (ha : 0 < a) (hw : 0 < w) (had : a+w < d)
    (hr : (a+w/2)/(d+w/2) < r) (hr1 : r < 1) :
    Backflow c (twoBand a (a+w) d (d+w) r) 0 0 := by
  have hd : 0 < d+w/2 := by linarith
  have hf : a+w/2 < r*(d+w/2) := (div_lt_iff₀ hd).mp hr
  apply twoBand_backflow hc ha (by linarith) had (by linarith)
  · nlinarith [mul_pos hw (sub_pos.mpr hr1)]
  · have h := mul_neg_of_pos_of_neg hw (sub_neg.mpr hf)
    nlinarith

/-- The generalized construction can be placed at any prescribed position and time. -/
theorem shifted_twoBand_backflow {a b d e r c : ℝ} (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hbd : b < d) (hde : d < e)
    (hzero : 0 < (b-a)-r*(e-d))
    (hfirst : (b^2-a^2)/2-r*((e^2-d^2)/2) < 0) (t₀ x₀ : ℝ) :
    Backflow c (shiftedProfile c t₀ x₀ (twoBand a b d e r)) x₀ t₀ := by
  let φ := twoBand a b d e r
  have hb := twoBand_backflow hc ha hab hbd hde hzero hfirst
  apply backflow_of_regular ((regular_twoBand c r hab.le hde.le).of_shiftedProfile t₀ x₀)
    (integrable_shiftedProfile c t₀ x₀ (integrable_twoBand a b d e r))
    (by simpa using (integrable_moment_shiftedProfile c t₀ x₀ 1 (integrable_weighted_twoBand a b d e r 1)))
    (integrable_moment_shiftedProfile c t₀ x₀ 2 (integrable_weighted_twoBand a b d e r 2))
  · simpa only [normSq_shiftedProfile] using hb.momentum_integrable
  · simpa only [normSq_shiftedProfile] using hb.momentum_mass_pos
  · intro p hp
    rw [shiftedProfile_eq_zero_iff]
    exact twoBand_positive_support ha (by linarith) hp
  · simpa only [momentumCurrent_shiftedProfile, sub_self] using
      twoBand_current_negative hc hab.le hde.le hzero hfirst

/-- Backflow exists at every spacetime point and every positive free-particle coefficient. -/
theorem quantum_backflow_exists {c : ℝ} (hc : 0 < c) (t₀ x₀ : ℝ) :
    ∃ φ : ℝ → ℂ, Backflow c φ x₀ t₀ := by
  exact ⟨shiftedProfile c t₀ x₀ (twoBand 1 2 3 4 (1/2)),
    shifted_twoBand_backflow hc (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) t₀ x₀⟩

end QuantumBackflow
