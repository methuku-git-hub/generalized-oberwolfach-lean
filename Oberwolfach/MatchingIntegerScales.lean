module

public import Oberwolfach.AsymptoticMargins
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

@[expose] public section

/-! Integer parameter choices for the fixed-error weighted matching theorem.
The scale is chosen from the host order, independently of the hypergraph and
the prescribed test functions. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem matching_integer_root_scale (a H n : ℕ) (ha : 0<a) (hH : 2≤H)
    (hn : H^a≤n) :
    let h := Nat.nthRoot a n
    H≤h ∧ h^a≤n ∧ n≤h^(2*a) := by
  dsimp only
  have hHh : H≤Nat.nthRoot a n := (Nat.le_nthRoot_iff (by omega)).mpr hn
  have hh : 2≤Nat.nthRoot a n := hH.trans hHh
  refine ⟨hHh,(Nat.pow_nthRoot_le_iff).mpr (Or.inl (by omega)),?_⟩
  have hnext := (Nat.lt_pow_nthRoot_add_one (by omega : a≠0) n).le
  have hs : Nat.nthRoot a n+1≤(Nat.nthRoot a n)^2 := by nlinarith
  calc
    _ ≤ (Nat.nthRoot a n+1)^a := hnext
    _ ≤ ((Nat.nthRoot a n)^2)^a := Nat.pow_le_pow_left hs a
    _ = _ := (pow_mul _ _ _).symm

theorem matching_edge_split_scale (k h D : ℕ) (hk : 2≤k) (hh : 2≤h)
    (η : ℝ) (hη : 0<η) (hη1 : η≤1/100) (hηh : 1≤η*(h : ℝ)^4)
    (hD : h^(16*k)≤D) :
    let p := h^16
    let q := D/h^(16*k-12)
    let d := ⌈(1+4*η)*(h : ℝ)^4⌉₊
    let l := ⌈(1+η)*(d : ℝ)⌉₊
    0<q ∧ q≤D ∧ h^4≤d ∧
    (1+5*η)*(h : ℝ)^4≤l ∧ (l : ℝ)≤(1+8*η)*(h : ℝ)^4 ∧
    (D : ℝ)≤(p : ℝ)^(k-1)*q*l ∧
    (p : ℝ)^(k-1)*q*l≤(1+8*η)*D ∧
    (1+η)*(D : ℝ)/((p : ℝ)^(k-1)*q)≤(1+3*η)*(h : ℝ)^4 := by
  dsimp only
  let m := h^(16*k-12)
  let q := D/m
  let d := ⌈(1+4*η)*(h : ℝ)^4⌉₊
  let l := ⌈(1+η)*(d : ℝ)⌉₊
  have hh0 : 0<h := by omega
  have hhR : (1 : ℝ)≤h := by exact_mod_cast (show 1≤h by omega)
  have hm : 0<m := pow_pos hh0 _
  have hmR : (0 : ℝ)<m := Nat.cast_pos.mpr hm
  have hDpos : (0 : ℝ)<D := Nat.cast_pos.mpr (lt_of_lt_of_le (pow_pos hh0 _) hD)
  have hprod : m*h^12=h^(16*k) := by
    dsimp [m]
    rw [← pow_add]
    congr 1;omega
  have hmD : m≤D := by
    calc
      _ ≤ h^(16*k) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := hD
  have hq : 0<q := Nat.div_pos hmD hm
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hmul : m*q≤D := Nat.mul_div_le _ _
  have hfloor : D<m*q+m := by
    have hd := Nat.mod_lt D hm
    have he := Nat.mod_add_div D m
    dsimp only [q]
    omega
  have h12 : 1≤η*(h : ℝ)^12 :=
    hηh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hhR (by omega : 4≤12)) hη.le)
  have hmηD : (m : ℝ)≤η*D := by
    have hh' : (m : ℝ)*(h : ℝ)^12≤D := by exact_mod_cast (hprod ▸ hD)
    nlinarith [mul_le_mul_of_nonneg_left h12 hmR.le,mul_le_mul_of_nonneg_left hh' hη.le]
  have hmq : (1-η)*(D : ℝ)≤(m : ℝ)*q := by
    have hf : (D : ℝ)<(m : ℝ)*q+m := by exact_mod_cast hfloor
    linarith
  have hscale : ((h^16 : ℕ) : ℝ)^(k-1)*(q : ℝ)*(h : ℝ)^4=(m : ℝ)*q := by
    push_cast
    rw [← pow_mul]
    have he : (h : ℝ)^(16*(k-1))*(h : ℝ)^4=(h : ℝ)^(16*k-12) := by
      rw [← pow_add];congr 1;omega
    dsimp [m]
    push_cast
    calc
      _ = ((h : ℝ)^(16*(k-1))*(h : ℝ)^4)*q := by ring
      _ = _ := by rw [he]
  have hdlo : (1+4*η)*(h : ℝ)^4≤d := Nat.le_ceil _
  have hdhi : (d : ℝ)≤(1+5*η)*(h : ℝ)^4 := by
    have hf := Nat.ceil_lt_add_one (show 0≤(1+4*η)*(h : ℝ)^4 by positivity)
    change (d : ℝ)<_ at hf
    nlinarith
  have hdl : h^4≤d := by
    have hh' : (h : ℝ)^4≤d := by nlinarith [pow_nonneg (show (0 : ℝ)≤h from Nat.cast_nonneg h) 4]
    exact_mod_cast hh'
  have hllo : (1+5*η)*(h : ℝ)^4≤l := by
    have hh' := mul_le_mul_of_nonneg_left hdlo (show 0≤1+η by positivity)
    have hl' : (1+η)*(d : ℝ)≤l := Nat.le_ceil _
    nlinarith [sq_nonneg η,pow_nonneg (show (0 : ℝ)≤h from Nat.cast_nonneg h) 4]
  have hlhi : (l : ℝ)≤(1+8*η)*(h : ℝ)^4 := by
    have hf := Nat.ceil_lt_add_one (show 0≤(1+η)*(d : ℝ) by positivity)
    change (l : ℝ)<_ at hf
    have hh' := mul_le_mul_of_nonneg_left hdhi (show 0≤1+η by positivity)
    have hηsq : 5*η^2≤η := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hηsq (show 0≤(h : ℝ)^4 by positivity)]
  have hpq : 0<((h^16 : ℕ) : ℝ)^(k-1)*(q : ℝ) := by positivity
  refine ⟨hq,Nat.div_le_self _ _,hdl,hllo,hlhi,?_,?_,?_⟩
  · have hbase := mul_le_mul_of_nonneg_left hmq (show 0≤1+5*η by positivity)
    have hl' := mul_le_mul_of_nonneg_left hllo hpq.le
    have hid : ((h^16 : ℕ) : ℝ)^(k-1)*(q : ℝ)*((1+5*η)*(h : ℝ)^4)=(1+5*η)*((m : ℝ)*q) := by
      calc
        _ = (1+5*η)*(((h^16 : ℕ) : ℝ)^(k-1)*q*(h : ℝ)^4) := by ring
        _ = _ := by rw [hscale]
    rw [hid] at hl'
    have hηsq : 5*η^2≤4*η := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hηsq hDpos.le]
  · have hl' := mul_le_mul_of_nonneg_left hlhi hpq.le
    have hmulR : (m : ℝ)*q≤D := by exact_mod_cast hmul
    calc
      _ ≤ ((h^16 : ℕ) : ℝ)^(k-1)*q*((1+8*η)*(h : ℝ)^4) := hl'
      _ = (1+8*η)*((m : ℝ)*q) := by
        calc
          _ = (1+8*η)*(((h^16 : ℕ) : ℝ)^(k-1)*q*(h : ℝ)^4) := by ring
          _ = _ := by rw [hscale]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmulR (by positivity)
  · apply (div_le_iff₀ hpq).mpr
    have hbase := mul_le_mul_of_nonneg_left hmq (show 0≤1+3*η by positivity)
    have hηsq : 3*η^2≤η := by nlinarith
    calc
      _ ≤ (1+3*η)*((m : ℝ)*q) := by nlinarith [mul_le_mul_of_nonneg_right hηsq hDpos.le]
      _ = _ := by rw [← hscale];ring

end Oberwolfach
