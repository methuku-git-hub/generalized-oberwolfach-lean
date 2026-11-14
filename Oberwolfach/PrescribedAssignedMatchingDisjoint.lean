module

public import Oberwolfach.PrescribedMatchingOccurrenceBound

@[expose] public section
/-! Assigning each physical bad edge to one index makes the resulting
matching edge sets pairwise disjoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem prescribed_assigned_matchings_disjoint (M:I→Finset (V×V))
    (K:SimpleGraph V) (assign:Sym2 V→I)
    (hassign:∀i e,e∈(M i).image prescribedArcPhysical→e∈K.edgeFinset ∧ assign e=i):
    (∀i,(M i).image prescribedArcPhysical⊆K.edgeFinset) ∧
    PairwisePhysicalDisjoint (fun i=>(M i).image prescribedArcPhysical) := by
  constructor
  · intro i e he;exact (hassign i e he).1
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact hij ((hassign i e hei).2.symm.trans (hassign j e hej).2)
end Oberwolfach
