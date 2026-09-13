import QuantumBackflow.FreeEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory Complex Set
open scoped Topology

noncomputable section

namespace QuantumBackflow

/-- Fourier integral of an amplitude over a finite momentum interval. -/
def finiteFourier (u : ℝ → ℂ) (a b x : ℝ) : ℂ :=
  ∫ p in a..b, u p * phase (p * x)

lemma norm_finiteFourier_le {u : ℝ → ℂ} {a b A : ℝ} (hab : a ≤ b)
    (hu : ∀ p ∈ Icc a b, ‖u p‖ ≤ A) (x : ℝ) :
    ‖finiteFourier u a b x‖ ≤ (b - a) * A := by
  unfold finiteFourier
  convert intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := A) (f := fun p => u p * phase (p*x)) ?_ using 1
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    ring
  · intro p hp
    simp only [uIoc_of_le hab] at hp
    simpa using hu p ⟨hp.1.le, hp.2⟩

/-- Integration by parts provides a frequency-weighted bound without dividing by frequency. -/
lemma abs_mul_norm_finiteFourier_le {u u' : ℝ → ℂ} {a b A B : ℝ}
    (hab : a ≤ b) (hdu : ∀ p, HasDerivAt u (u' p) p)
    (hcont : Continuous u')
    (hu : ∀ p ∈ Icc a b, ‖u p‖ ≤ A)
    (hu' : ∀ p ∈ Icc a b, ‖u' p‖ ≤ B) (x : ℝ) :
    |x| * ‖finiteFourier u a b x‖ ≤ 2 * A + (b - a) * B := by
  let v : ℝ → ℂ := fun p => phase (p*x)
  let v' : ℝ → ℂ := fun p => ((x : ℂ) * I) * v p
  have hdv (p : ℝ) : HasDerivAt v (v' p) p := by
    convert (hasDerivAt_phase (p*x)).scomp p ((hasDerivAt_id p).mul_const x) using 1
    simp only [v, v', one_mul, Complex.real_smul]
    ring
  have hc : Continuous u := continuous_iff_continuousAt.mpr fun p => (hdu p).continuousAt
  have hcv : Continuous v := by dsimp [v]; fun_prop
  have hcv' : Continuous v' := by dsimp [v']; fun_prop
  have heq := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := a) (b := b) hc.continuousOn hcv.continuousOn
    (fun p _ => hdu p) (fun p _ => hdv p)
    (hcont.intervalIntegrable a b) (hcv'.intervalIntegrable a b)
  have hleft : (∫ p in a..b, u p * v' p) =
      ((x : ℂ) * I) * finiteFourier u a b x := by
    simp only [v', v, finiteFourier]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext p
    ring
  rw [hleft] at heq
  have hnorm : ‖((x : ℂ) * I) * finiteFourier u a b x‖ =
      |x| * ‖finiteFourier u a b x‖ := by simp
  rw [← hnorm, heq]
  calc
    ‖u b * v b - u a * v a - ∫ p in a..b, u' p * v p‖
        ≤ ‖u b * v b‖ + ‖u a * v a‖ + ‖∫ p in a..b, u' p * v p‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ A + A + (b-a)*B := by
      apply add_le_add
      · apply add_le_add
        · simpa [v] using hu b ⟨hab, le_rfl⟩
        · simpa [v] using hu a ⟨le_rfl, hab⟩
      · exact norm_finiteFourier_le hab hu' x
    _ = 2*A+(b-a)*B := by ring

private lemma phase_add_for_decay (r s : ℝ) : phase (r+s) = phase r * phase s := by
  simp [phase, add_mul, Complex.exp_add]

/-- Polynomial momentum moments of a freely evolving finite band. -/
def bandMoment (c : ℝ) (k : ℕ) (a b t x : ℝ) : ℂ :=
  ∫ p in a..b, (p : ℂ)^k * phase (p*x-c*p^2*t)

private def bandAmplitude (c : ℝ) (k : ℕ) (t p : ℝ) : ℂ :=
  (p : ℂ)^k * phase (-c*p^2*t)

private def bandAmplitudeDeriv (c : ℝ) (k : ℕ) (t p : ℝ) : ℂ :=
  ((k : ℂ)*(p : ℂ)^(k-1) + (p : ℂ)^k * (((-2*c*p*t : ℝ) : ℂ)*I)) *
    phase (-c*p^2*t)

private lemma hasDerivAt_bandAmplitude (c : ℝ) (k : ℕ) (t p : ℝ) :
    HasDerivAt (bandAmplitude c k t) (bandAmplitudeDeriv c k t p) p := by
  have hp : HasDerivAt (fun q : ℝ => -c*q^2*t) (-2*c*p*t) p := by
    convert (((hasDerivAt_id p).pow 2).const_mul (-c)).mul_const t using 1
    dsimp
    ring
  convert (((hasDerivAt_id p).ofReal_comp.pow k).mul
    ((hasDerivAt_phase (-c*p^2*t)).scomp p hp)) using 1
  dsimp [bandAmplitudeDeriv]
  simp only [mul_one]
  ring

lemma bandMoment_eq_finiteFourier (c : ℝ) (k : ℕ) (a b t x : ℝ) :
    bandMoment c k a b t x =
      finiteFourier (fun p => (p : ℂ)^k * phase (-c*p^2*t)) a b x := by
  unfold bandMoment finiteFourier
  congr 1
  ext p
  have he : p*x-c*p^2*t = -c*p^2*t+p*x := by ring
  rw [he, phase_add_for_decay]
  ring

/-- Every polynomial band moment is bounded and decays as `1 / |x|`,
uniformly on a bounded time interval. Constants are deliberately not optimized. -/
lemma exists_bandMoment_bounds (c : ℝ) (k : ℕ) {a b : ℝ} (hab : a ≤ b) (T : ℝ) :
    ∃ B D : ℝ, 0 < B ∧ 0 < D ∧ ∀ t : ℝ, |t| ≤ T → ∀ x : ℝ,
      ‖bandMoment c k a b t x‖ ≤ B ∧ |x| * ‖bandMoment c k a b t x‖ ≤ D := by
  let K : Set (ℝ × ℝ) := Icc (-T) T ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hu : Continuous (fun tp : ℝ × ℝ => bandAmplitude c k tp.1 tp.2) := by
    unfold bandAmplitude
    fun_prop
  have hv : Continuous (fun tp : ℝ × ℝ => bandAmplitudeDeriv c k tp.1 tp.2) := by
    unfold bandAmplitudeDeriv
    fun_prop
  obtain ⟨A, hA, hAb⟩ := (hK.image hu).isBounded.exists_pos_norm_le
  obtain ⟨E, hE, hEb⟩ := (hK.image hv).isBounded.exists_pos_norm_le
  have hba : 0 ≤ b-a := sub_nonneg.mpr hab
  refine ⟨(b-a)*A+1, 2*A+(b-a)*E+1, by positivity, by positivity, ?_⟩
  intro t ht x
  have htK : t ∈ Icc (-T) T := abs_le.mp ht
  have hAu (p : ℝ) (hp : p ∈ Icc a b) : ‖bandAmplitude c k t p‖ ≤ A :=
    hAb _ ⟨(t,p), ⟨htK, hp⟩, rfl⟩
  have hEu (p : ℝ) (hp : p ∈ Icc a b) : ‖bandAmplitudeDeriv c k t p‖ ≤ E :=
    hEb _ ⟨(t,p), ⟨htK, hp⟩, rfl⟩
  rw [bandMoment_eq_finiteFourier]
  constructor
  · exact (norm_finiteFourier_le hab hAu x).trans (by linarith)
  · refine (abs_mul_norm_finiteFourier_le hab (hasDerivAt_bandAmplitude c k t)
      ?_ hAu hEu x).trans (by linarith)
    unfold bandAmplitudeDeriv
    fun_prop

/-- Two `1 / |x|` estimates combine with uniform bounds into an everywhere
valid integrable majorant. -/
lemma norm_product_le_decay {z w : ℂ} {x Bz Bw Dz Dw : ℝ}
    (hz : ‖z‖ ≤ Bz) (hw : ‖w‖ ≤ Bw)
    (hdz : |x| *‖z‖ ≤ Dz) (hdw : |x| *‖w‖ ≤ Dw) :
    ‖z‖ * ‖w‖ ≤ (Bz*Bw+Dz*Dw)/(1+x^2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1+x^2)).mpr
  have hB := mul_le_mul hz hw (norm_nonneg w) ((norm_nonneg z).trans hz)
  have hD := mul_le_mul hdz hdw (mul_nonneg (abs_nonneg x) (norm_nonneg w))
    ((mul_nonneg (abs_nonneg x) (norm_nonneg z)).trans hdz)
  have hrewrite : (|x| *‖z‖) * (|x| *‖w‖) = x^2*(‖z‖*‖w‖) := by
    calc
      _ = |x| ^2*(‖z‖*‖w‖) := by ring
      _ = _ := by rw [sq_abs]
  rw [hrewrite] at hD
  nlinarith

end QuantumBackflow
