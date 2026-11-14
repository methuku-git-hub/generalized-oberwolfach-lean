module

public import Oberwolfach.FiniteFibreCounts

@[expose] public section

/-! Finite union bounds for cardinalities, retaining the original index
sets even when their events overlap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_exists_card_le_sum {A I : Type*} [Fintype A] [Fintype I] (P : I → A → Prop) :
    Fintype.card {a : A // ∃ i,P i a} ≤ ∑ i,Fintype.card {a : A // P i a} := by
  classical
  let S := fun i => Finset.univ.filter (P i)
  have he : Finset.univ.filter (fun a => ∃ i,P i a)=Finset.univ.biUnion S := by
    ext a;simp [S]
  simp only [Fintype.card_subtype]
  rw [he]
  exact Finset.card_biUnion_le

end Oberwolfach
