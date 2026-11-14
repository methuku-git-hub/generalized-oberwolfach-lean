module

public import Oberwolfach.ResourceDecompositions
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Exact finite fibre counts used when forgetting root assignments and
external factors of a labelled absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_sigma_predicate_card {I : Type*} [Fintype I] {D : I → Type*}
    [∀ i,Fintype (D i)] (P : ∀ i,D i → Prop) :
    Fintype.card {d : Σ i,D i // P d.1 d.2}=∑ i,Fintype.card {d : D i // P i d} := by
  let e : {d : Σ i,D i // P d.1 d.2} ≃ Σ i,{d : D i // P i d} := {
    toFun d := ⟨d.val.1,⟨d.val.2,d.property⟩⟩
    invFun d := ⟨⟨d.1,d.2.val⟩,d.2.property⟩
    left_inv := by rintro ⟨⟨i,d⟩,h⟩;rfl
    right_inv := by rintro ⟨i,⟨d,h⟩⟩;rfl }
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

theorem finite_fibre_card_identity {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    Fintype.card A=∑ b,Fintype.card {a : A // f a=b} := by
  let e : A ≃ Σ b,{a : A // f a=b} := {
    toFun a := ⟨f a,⟨a,rfl⟩⟩
    invFun b := b.2.val
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨b,⟨a,h⟩⟩;subst b;rfl }
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

theorem finite_fibre_card_bound {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (M : ℕ) (hf : ∀ b,Fintype.card {a : A // f a=b} ≤ M) :
    Fintype.card A ≤ Fintype.card B*M := by
  rw [finite_fibre_card_identity f]
  calc
    _ ≤ ∑ _b : B,M := Finset.sum_le_sum (fun b _ => hf b)
    _ = _ := by simp

end Oberwolfach
