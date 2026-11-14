module

public import Oberwolfach.OrdinaryAdmissibleCycleLoads

@[expose] public section

/-! Normalize the conflict-free part of the original fractional cycle
weighting using the parent degree parameter. The weights are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_normalized_admissible_vertex_load {V:Type} [Fintype V] [DecidableEq V]
    (P F:SimpleGraph V) (r:ℕ) (hr:2≤r) (hn:0<Fintype.card V)
    (weight:OrdinaryCycle P r→ℝ) (hweight:∀ C,0≤weight C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (L:ℝ) (hdeg:∀ v,(F.degree v:ℝ)≤L)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (D ε:ℝ) (hD:0<D) (hnear:∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) (v:V):
    |(2/D)*(∑ C,if v∈C.val.val.support ∧
        (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) then weight C else 0)-1|≤
      (6*(r:ℝ)^4*B*L+ε*Fintype.card V)/D := by
  let S:ℝ:=∑ C,if v∈C.val.val.support ∧
    (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) then weight C else 0
  have hs:|S-(P.degree v:ℝ)/2|≤3*(r:ℝ)^4*B*L:=by
    have hh:=ordinary_admissible_cycle_vertex_load P F r hr hn weight hweight B hB hb L hdeg he v
    convert hh using 1 <;> congr!
  have ha:=abs_le.mp hs
  have hd:=abs_le.mp (hnear v)
  have hraw:|2*S-D|≤6*(r:ℝ)^4*B*L+ε*Fintype.card V:=by
    apply abs_le.mpr
    constructor <;> linarith only [ha.1,ha.2,hd.1,hd.2]
  have heq:(2/D)*S-1=(2*S-D)/D:=by field_simp
  change |(2/D)*S-1|≤_
  rw [heq,abs_div,abs_of_pos hD]
  exact div_le_div_of_nonneg_right hraw hD.le
end Oberwolfach
