module

public import Mathlib.Tactic

@[expose] public section

/-! The actual constants for the copied marked-capacity graph. These estimates
use the degree target pD/(k+1); the transition bounds retain the actual p. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem marked_transition_entry_bounds (k : ℕ) (p D n a d : ℝ)
    (hp : 0<p) (hn : 0<n) (hDlo : n/2≤D) (hDhi : D≤2*n)
    (ha : 1/(2*(k+1:ℝ))≤a ∧ a≤2/(k+1:ℝ))
    (hd : (9/10)*(p*D/(k+1:ℝ))≤d ∧ d≤(11/10)*(p*D/(k+1:ℝ))) :
    1/(6*p*n)≤a/d ∧ a/d≤5/(p*n) := by
  have hkp : (0:ℝ)<k+1 := by positivity
  have hDp : 0<D := by linarith
  have hdp : 0<d := (by positivity : 0<(9/10)*(p*D/(k+1:ℝ))).trans_le hd.1
  have hdl : (9/10)*(p*(n/2)/(k+1:ℝ))≤d := by
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDlo hp.le) hkp.le) (by norm_num)).trans hd.1
  have hdu : d≤(11/10)*(p*(2*n)/(k+1:ℝ)) := by
    exact hd.2.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDhi hp.le) hkp.le) (by norm_num))
  constructor
  · apply (le_div_iff₀ hdp).mpr
    calc
      (1/(6*p*n))*d ≤ (1/(6*p*n))*((11/10)*(p*(2*n)/(k+1:ℝ))) :=
        mul_le_mul_of_nonneg_left hdu (by positivity)
      _ ≤ 1/(2*(k+1:ℝ)) := by field_simp; nlinarith
      _ ≤ a := ha.1
  · apply (div_le_iff₀ hdp).mpr
    calc
      a ≤ 2/(k+1:ℝ) := ha.2
      _ ≤ (5/(p*n))*((9/10)*(p*(n/2)/(k+1:ℝ))) := by field_simp; nlinarith
      _ ≤ (5/(p*n))*d := mul_le_mul_of_nonneg_left hdl (by positivity)

theorem marked_stationary_bounds {V : Type*} [Fintype V]
    (d : V → ℝ) (q M : ℝ) (hn : 0<Fintype.card V) (hq : 0<q)
    (hd : ∀ v,(9/10)*q≤d v ∧ d v≤(11/10)*q)
    (htotal : ∑ v,d v=M) (v : V) :
    1/(2*(Fintype.card V:ℝ))≤d v/M ∧ d v/M≤2/(Fintype.card V:ℝ) := by
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hMlo : (Fintype.card V:ℝ)*((9/10)*q)≤M := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => (hd x).1)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,htotal] using hh
  have hMhi : M≤(Fintype.card V:ℝ)*((11/10)*q) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => (hd x).2)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,htotal] using hh
  have hMp : 0<M := (by positivity : 0<(Fintype.card V:ℝ)*((9/10)*q)).trans_le hMlo
  constructor
  · apply (le_div_iff₀ hMp).mpr
    calc
      (1/(2*(Fintype.card V:ℝ)))*M ≤ (1/(2*(Fintype.card V:ℝ)))*((Fintype.card V:ℝ)*((11/10)*q)) :=
        mul_le_mul_of_nonneg_left hMhi (by positivity)
      _ ≤ (9/10)*q := by field_simp; nlinarith
      _ ≤ d v := (hd v).1
  · apply (div_le_iff₀ hMp).mpr
    calc
      d v ≤ (11/10)*q := (hd v).2
      _ ≤ (2/(Fintype.card V:ℝ))*((Fintype.card V:ℝ)*((9/10)*q)) := by field_simp; nlinarith
      _ ≤ (2/(Fintype.card V:ℝ))*M := mul_le_mul_of_nonneg_left hMlo (by positivity)

theorem marked_capacity_degree_scales (k : ℕ) (p p₀ D n d : ℝ)
    (hp₀ : 0<p₀) (hp : p₀≤p) (hpmax : p≤1/2) (hn : 0<n)
    (hDlo : n/2≤D) (hDhi : D≤2*n)
    (hd : (9/10)*(p*D/(k+1:ℝ))≤d ∧ d≤(11/10)*(p*D/(k+1:ℝ))) :
    (p₀/(3*(k+1:ℝ)))*n≤d ∧ d≤(2/(k+1:ℝ))*n := by
  have hkp : (0:ℝ)<k+1 := by positivity
  have hpp : 0<p := hp₀.trans_le hp
  have hD : 0<D := by linarith
  have hl : p₀*n/2≤p*D := by nlinarith [mul_le_mul_of_nonneg_right hp hD.le]
  have hu : p*D≤n := by nlinarith [mul_le_mul_of_nonneg_left hDhi hpp.le]
  have hlo := (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hl hkp.le) (show (0:ℝ)≤9/10 by norm_num)).trans hd.1
  have hhi := hd.2.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hu hkp.le) (show (0:ℝ)≤11/10 by norm_num))
  constructor
  · apply le_trans _ hlo
    field_simp
    <;> nlinarith
  · apply le_trans hhi
    field_simp
    <;> nlinarith

theorem marked_transition_domination (p p₀ n R μ : ℝ)
    (hp₀ : 0<p₀) (hp : p₀≤p) (hn : 0<n)
    (hR : R≤5/(p*n)) (hμ : 1/(2*n)≤μ) : R≤(100/p₀)*μ := by
  have hpp : 0<p := hp₀.trans_le hp
  calc
    R ≤ 5/(p*n) := hR
    _ ≤ 5/(p₀*n) := div_le_div_of_nonneg_left (by norm_num) (mul_pos hp₀ hn)
      (mul_le_mul_of_nonneg_right hp hn.le)
    _ ≤ (100/p₀)*(1/(2*n)) := by field_simp; nlinarith
    _ ≤ (100/p₀)*μ := mul_le_mul_of_nonneg_left hμ (by positivity)

end Oberwolfach
