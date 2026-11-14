module

public import Oberwolfach.EdgeRetention
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-! The actual activation and colour probabilities in the raw interval
experiment. Their validity is proved from the manuscript's profile bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def intervalActivation (d : ℕ) : ℝ := 1/(2*(d:ℝ)+1)
def isolatedStartProbability (d : ℕ) : ℝ :=
  intervalActivation d*(1-intervalActivation d)^(2*d)

theorem intervalActivation_bounds (d : ℕ) (hd : 2≤d) :
    0 < intervalActivation d ∧ intervalActivation d<1 := by
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  unfold intervalActivation
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).mpr (by linarith)

theorem isolatedStartProbability_pos (d : ℕ) (hd : 2≤d) :
    0 < isolatedStartProbability d :=
  mul_pos (intervalActivation_bounds d hd).1 (pow_pos (sub_pos.mpr (intervalActivation_bounds d hd).2) _)

theorem isolatedStartProbability_scaled_lower (d : ℕ) (hd : 2≤d) :
    (2:ℝ)/15<(d:ℝ)*isolatedStartProbability d := by
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := by linarith
  have he : (1+(1/(2*(d:ℝ))))^(2*d)<3 := by
    have hh := (Real.one_add_inv_pow_le_exp (n:=2*d)).trans_lt Real.exp_one_lt_three
    simpa only [Nat.cast_mul,Nat.cast_ofNat,one_div] using hh
  have hbase : 1-intervalActivation d=(1+1/(2*(d:ℝ)))⁻¹ := by
    unfold intervalActivation
    field_simp
    <;> ring
  have hpos : 0<(1+1/(2*(d:ℝ)))^(2*d) := by positivity
  have hp : (1:ℝ)/3<(1-intervalActivation d)^(2*d) := by
    rw [hbase,inv_pow]
    simpa only [one_div] using inv_lt_inv₀ (by norm_num : (0:ℝ)<3) hpos |>.mpr he
  have hdfrac : (2:ℝ)/5≤(d:ℝ)/(2*d+1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hd']
  have hmul := mul_lt_mul_of_pos_left hp (by positivity : 0<(d:ℝ)/(2*d+1))
  have hprod := mul_le_mul_of_nonneg_right hdfrac (by norm_num : (0:ℝ)≤1/3)
  have hh := hprod.trans_lt hmul
  calc
    (2:ℝ)/15 = (2/5)*(1/3) := by norm_num
    _ < (d:ℝ)/(2*d+1)*(1-intervalActivation d)^(2*d) := hh
    _ = (d:ℝ)*isolatedStartProbability d := by
      unfold isolatedStartProbability intervalActivation
      ring

/-- A finite subprobability vector with the remaining mass at `none`. -/
def FiniteLaw.withRemainder {Γ : Type*} [Fintype Γ]
    (q : Γ → ℝ) (hq : ∀ g,0≤q g) (hQ : ∑ g,q g≤1) : FiniteLaw (Option Γ) where
  mass g := match g with | none=>1-∑ g,q g | some g=>q g
  nonneg g := by cases g <;> simp only;linarith;exact hq _
  total := by rw [Fintype.sum_option];simp

theorem rawInterval_start_probabilities {Γ : Type*} [Fintype Γ]
    (d : ℕ) (hd : 2≤d) (q : Γ → ℝ) (hq : ∀ g,0≤q g) (hQ : ∑ g,q g≤1/8) :
    (∀ g,0≤q g/((d:ℝ)*isolatedStartProbability d)) ∧
      (∑ g,q g/((d:ℝ)*isolatedStartProbability d))≤1 := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hr := isolatedStartProbability_pos d hd
  refine ⟨fun g=>div_nonneg (hq g) (mul_pos hd0 hr).le,?_⟩
  rw [← Finset.sum_div]
  apply (div_le_one (mul_pos hd0 hr)).mpr
  have hh := isolatedStartProbability_scaled_lower d hd
  linarith

def rawIntervalStartLaw {Γ : Type*} [Fintype Γ]
    (d : ℕ) (hd : 2≤d) (q : Γ → ℝ) (hq : ∀ g,0≤q g) (hQ : ∑ g,q g≤1/8) :
    FiniteLaw (Option Γ) :=
  FiniteLaw.withRemainder (fun g=>q g/((d:ℝ)*isolatedStartProbability d))
    (rawInterval_start_probabilities d hd q hq hQ).1
    (rawInterval_start_probabilities d hd q hq hQ).2

def intervalUncoveredProbability (d : ℕ) (Q : ℝ) : ℝ := 1-(1+1/(d:ℝ))*Q

theorem intervalUncoveredProbability_lower (d : ℕ) (hd : 2≤d) (Q : ℝ)
    (hQ0 : 0≤Q) (hQ : Q≤1/8) : (13:ℝ)/16≤ intervalUncoveredProbability d Q := by
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  have hinv : 1/(d:ℝ)≤1/2 := (div_le_div_iff₀ (by linarith) (by norm_num)).mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_right (show 1+1/(d:ℝ)≤3/2 by linarith) hQ0
  unfold intervalUncoveredProbability
  nlinarith only [hh,hQ]

def rawIntervalLabelLaw {Color : Type*} [Fintype Color]
    (d : ℕ) (hd : 2≤d) (Q : ℝ) (hQ0 : 0≤Q) (hQ : Q≤1/8)
    (s : Color → ℝ) (hs : ∀ j,0≤s j) (hS : ∑ j,s j≤ intervalUncoveredProbability d Q) :
    FiniteLaw (Option Color) :=
  FiniteLaw.withRemainder (fun j=>s j/intervalUncoveredProbability d Q)
    (fun j=>div_nonneg (hs j) (by have hh:=intervalUncoveredProbability_lower d hd Q hQ0 hQ;linarith))
    (by
      rw [← Finset.sum_div]
      apply (div_le_one (by have hh:=intervalUncoveredProbability_lower d hd Q hQ0 hQ;linarith)).mpr
      exact hS)

end Oberwolfach
