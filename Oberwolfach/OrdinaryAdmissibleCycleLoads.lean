module

public import Oberwolfach.OrdinaryCycleConflictLoss
public import Oberwolfach.CycleVertexMatchingWeights

@[expose] public section

/-! The fixed fractional cycle weighting after exclusion of cycles whose
vertex set contains a conflict edge. The original weights are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem finite_weight_discard_identity {I : Type*} [Fintype I]
    (weight : I → ℝ) (base good : I → Prop) :
    (∑ i,if base i then weight i else 0)-
      (∑ i,if base i ∧ good i then weight i else 0)=
      ∑ i,if base i ∧ ¬good i then weight i else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hb : base i <;> by_cases hg : good i <;> simp [hb,hg]

variable {V : Type} [Fintype V] [DecidableEq V]
    (P F : SimpleGraph V) (r : ℕ) (hr : 2≤r) (hn : 0<Fintype.card V)
    (weight : OrdinaryCycle P r → ℝ) (hweight : ∀ C,0≤weight C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (L : ℝ) (hdeg : ∀ v,(F.degree v:ℝ)≤L)
    (he : ∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
include hr hn hweight hB hb hdeg he

theorem ordinary_admissible_cycle_edge_load (x y : V) (hxy : P.Adj x y) (hFxy : ¬F.Adj x y) :
    |(∑ C,if C.val.val.Adj x y ∧ (∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z)
      then weight C else 0)-1|≤5*(r:ℝ)^4*B*L/Fintype.card V := by
  let good := fun C : OrdinaryCycle P r=>∀ v∈C.val.val.support,∀ z∈C.val.val.support,¬F.Adj v z
  have hnot (C : OrdinaryCycle P r) : ¬good C↔∃ v∈C.val.val.support,∃ z∈C.val.val.support,F.Adj v z := by
    simp only [good,not_forall,not_imp,not_not,exists_prop]
  have hid := finite_weight_discard_identity weight (fun C=>C.val.val.Adj x y) good
  rw [he x y,if_pos hxy] at hid
  simp only [hnot] at hid
  have hlo : 0≤∑ C,if C.val.val.Adj x y ∧ (∃ v∈C.val.val.support,∃ z∈C.val.val.support,F.Adj v z)
      then weight C else 0 := Finset.sum_nonneg (fun C _=>by split_ifs;exact hweight C;exact le_refl _)
  have hhi := ordinary_cycle_rim_conflict_loss P r hr hn weight hweight B hB hb F L hdeg x y hxy.ne hFxy
  have hbound : |(∑ C,if C.val.val.Adj x y ∧ good C then weight C else 0)-1|≤
      5*(r:ℝ)^4*B*L/Fintype.card V := by
    rw [abs_sub_comm]
    erw [hid]
    rw [abs_of_nonneg hlo]
    convert hhi using 1 <;> congr!
  convert hbound using 1 <;> congr!

theorem ordinary_admissible_cycle_vertex_load (v : V) :
    |(∑ C,if v∈C.val.val.support ∧ (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y)
      then weight C else 0)-(P.degree v:ℝ)/2|≤3*(r:ℝ)^4*B*L := by
  let good := fun C : OrdinaryCycle P r=>∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y
  have hnot (C : OrdinaryCycle P r) : ¬good C↔∃ x∈C.val.val.support,∃ y∈C.val.val.support,F.Adj x y := by
    simp only [good,not_forall,not_imp,not_not,exists_prop]
  have hv := ordinary_cycle_vertex_weight_identity P r weight he v
  simp only [ordinaryCycleVertices,Set.mem_toFinset] at hv
  have hfull : (∑ C,if v∈C.val.val.support then weight C else 0)=(P.degree v:ℝ)/2 := by
    have hv' : 2*(∑ C,if v∈C.val.val.support then weight C else 0)=(P.degree v:ℝ) := by
      convert hv using 1 <;> congr!
    linarith only [hv']
  have hid := finite_weight_discard_identity weight (fun C=>v∈C.val.val.support) good
  erw [hfull] at hid
  simp only [hnot] at hid
  have hlo : 0≤∑ C,if v∈C.val.val.support ∧ (∃ x∈C.val.val.support,∃ y∈C.val.val.support,F.Adj x y)
      then weight C else 0 := Finset.sum_nonneg (fun C _=>by split_ifs;exact hweight C;exact le_refl _)
  have hhi := ordinary_cycle_vertex_conflict_loss P r hr hn weight hweight B hB hb F L hdeg v
  have hbound : |(∑ C,if v∈C.val.val.support ∧ good C then weight C else 0)-(P.degree v:ℝ)/2|≤
      3*(r:ℝ)^4*B*L := by
    rw [abs_sub_comm]
    erw [hid]
    rw [abs_of_nonneg hlo]
    convert hhi using 1 <;> congr!
  convert hbound using 1 <;> congr!

end Oberwolfach
