module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Updating one factor preserves disjointness of physical edge images when
the added physical edges avoid all other factors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I R:Type} [DecidableEq I] [DecidableEq R]

def PairwisePhysicalDisjoint (E:I→Finset R):Prop:=
  ∀ i j,i≠j→Disjoint (E i) (E j)

theorem prescribed_embedding_disjoint_update (E:I→Finset R) (k:I) (added:Finset R)
    (hpair:PairwisePhysicalDisjoint E)
    (havoid:∀ j,j≠k→Disjoint added (E j)):
    PairwisePhysicalDisjoint (Function.update E k (E k∪added)) := by
  intro i j hij
  by_cases hi:i=k
  · subst i
    have hj:j≠k:=Ne.symm hij
    simp only [Function.update_self,Function.update_of_ne hj]
    exact Finset.disjoint_union_left.mpr ⟨hpair k j hij,havoid j hj⟩
  · by_cases hj:j=k
    · subst j
      simp only [Function.update_self,Function.update_of_ne hi]
      exact Finset.disjoint_union_right.mpr ⟨hpair i k hij,(havoid i hi).symm⟩
    · simp only [Function.update_of_ne hi,Function.update_of_ne hj]
      exact hpair i j hij
end Oberwolfach
