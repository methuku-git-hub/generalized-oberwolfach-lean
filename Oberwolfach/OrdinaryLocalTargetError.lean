module

public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section

/-! The original ordinary local target is close to one. The conflict
loss is applied before restricting to the sparse host; no density factor
is attached to the realized forbidden-pair deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinaryLocalTarget_error (P F : SimpleGraph V) (hr : 2≤r) (hn : 0<Fintype.card V)
    (weight : OrdinaryCycle P r→ℝ) (hweight : ∀ C,0≤weight C)
    (B L D δ : ℝ) (hB : 0≤B) (hL : 0≤L) (hδ : 0≤δ)
    (hweightB : ∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hedge : ∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (hD : (Fintype.card V:ℝ)/2≤D) (v : V) (hdeg : |(P.degree v:ℝ)-D|≤δ*Fintype.card V) :
    |ordinaryLocalTarget P F weight D v-1|≤2*δ+12*(r:ℝ)^4*B*L/Fintype.card V := by
  let n : ℝ := Fintype.card V
  have hnR : 0<n := Nat.cast_pos.mpr hn
  have hDpos : 0<D := (half_pos hnR).trans_le hD
  have hload := ordinary_admissible_cycle_vertex_load P F r hr hn weight hweight B hB hweightB L hF hedge v
  have hid : ordinaryLocalTarget P F weight D v-(P.degree v:ℝ)/D=
      (2/D)*((∑ C,if v∈C.val.val.support ∧
        (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) then weight C else 0)-(P.degree v:ℝ)/2) := by
    unfold ordinaryLocalTarget;ring
  have hmid : |ordinaryLocalTarget P F weight D v-(P.degree v:ℝ)/D|≤6*(r:ℝ)^4*B*L/D := by
    rw [hid,abs_mul,abs_of_nonneg (show 0≤2/D by positivity)]
    have hh := mul_le_mul_of_nonneg_left hload (show 0≤2/D by positivity)
    convert hh using 1 <;> ring
  have hlast : |(P.degree v:ℝ)/D-1|≤δ*n/D := by
    have he : (P.degree v:ℝ)/D-1=((P.degree v:ℝ)-D)/D := by field_simp
    rw [he,abs_div,abs_of_pos hDpos]
    exact div_le_div_of_nonneg_right hdeg hDpos.le
  have hlo : 6*(r:ℝ)^4*B*L/D≤12*(r:ℝ)^4*B*L/n := by
    have hh := div_le_div_of_nonneg_left (show 0≤6*(r:ℝ)^4*B*L by positivity) (half_pos hnR) hD
    convert hh using 1 <;> field_simp <;> ring
  have hhi : δ*n/D≤2*δ := by
    have hh := div_le_div_of_nonneg_left (show 0≤δ*n by positivity) (half_pos hnR) hD
    have he : δ*n/(n/2)=2*δ := by field_simp
    exact hh.trans_eq he
  have ht := abs_sub_le (ordinaryLocalTarget P F weight D v) ((P.degree v:ℝ)/D) 1
  linarith only [ht,hmid,hlast,hlo,hhi]

end Oberwolfach
