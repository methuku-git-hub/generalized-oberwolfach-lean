module

public import Oberwolfach.OrdinaryAddedEdgesEditDegree

@[expose] public section
/-! Removing a bounded reserved rim graph increases each symmetric edit
count by at most its degree. This permits protecting an absorber before
embedding the unreserved complements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_reserved_rim_edit_budget
    (Target Sample Reserve:SimpleGraph V) (v:V):
    (Finset.univ.filter (fun y=>Xor ((Target\Reserve).Adj v y) (Sample.Adj v y))).card≤
      (Finset.univ.filter (fun y=>Xor (Target.Adj v y) (Sample.Adj v y))).card+Reserve.degree v:=by
  let T:=Finset.univ.filter (fun y=>Xor ((Target\Reserve).Adj v y) (Sample.Adj v y))
  let C:=Finset.univ.filter (fun y=>Xor (Target.Adj v y) (Sample.Adj v y))
  let R:=Reserve.neighborFinset v
  have hsub:T⊆C∪R:=by
    intro y hy
    have ht:Xor ((Target\Reserve).Adj v y) (Sample.Adj v y):=(Finset.mem_filter.mp hy).2
    have hlog:Xor (Target.Adj v y) (Sample.Adj v y) ∨ Reserve.Adj v y:=by
      change Xor (Target.Adj v y ∧ ¬Reserve.Adj v y) (Sample.Adj v y) at ht
      by_cases ha:Target.Adj v y <;> by_cases hb:Sample.Adj v y <;>
        by_cases hc:Reserve.Adj v y <;> simp_all [Xor]
    rcases hlog with hc|hr
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩)
    · exact Finset.mem_union_right _ ((Reserve.mem_neighborFinset v y).mpr hr)
  have hc: T.card≤C.card+R.card:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have he:R.card=Reserve.degree v:=Reserve.card_neighborFinset_eq_degree v
  rw [he] at hc
  exact hc
end Oberwolfach
