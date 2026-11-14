module

public import Oberwolfach.PrescribedIndexOccurrenceUnion
public import Oberwolfach.PrescribedMatchingOccurrenceBound

@[expose] public section
/-! The augmented prescriptions have the original old-prescription, new
singleton and actual bad-edge degree contributions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem prescribed_augmented_occurrence_bound (P Z:I→Finset V) (M:I→Finset (V×V))
    (K:SimpleGraph V) (hsub:∀i,(M i).image prescribedArcPhysical⊆K.edgeFinset)
    (hpair:PairwisePhysicalDisjoint (fun i=>(M i).image prescribedArcPhysical)) (v:V):
    (Finset.univ.filter (fun i=>v∈P i∪prescribedMatchingEndpoints (M i)∪Z i)).card≤
      (Finset.univ.filter (fun i=>v∈P i)).card+K.degree v+
      (Finset.univ.filter (fun i=>v∈Z i)).card := by
  exact (prescribed_union_occurrence_bound P (fun i=>prescribedMatchingEndpoints (M i)) Z v).trans
    (Nat.add_le_add_right (Nat.add_le_add_left (prescribed_matching_endpoint_occurrences M K hsub hpair v) _) _)
end Oberwolfach
