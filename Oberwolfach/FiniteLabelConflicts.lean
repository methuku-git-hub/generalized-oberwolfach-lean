module

public import Oberwolfach.PermutationClose
public import Oberwolfach.FiniteFibreCounts

@[expose] public section

/-! Pulling permutation-distance balls back through a label map with
bounded fibres. Reindexing labels by a bijection preserves this bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem label_predicate_card_bound {A V : Type*} [Fintype A] [Fintype V]
    (f : A → V) (P : V → Prop) (M : ℕ)
    (hf : ∀ v, Fintype.card {a // f a=v} ≤ M) :
    Fintype.card {a // P (f a)} ≤ Fintype.card {v // P v} * M := by
  classical
  let g : {a // P (f a)} → {v // P v} := fun a => ⟨f a.val,a.property⟩
  apply finite_fibre_card_bound g M
  intro v
  let enc : {a // g a=v} → {a // f a=v.val} :=
    fun a => ⟨a.val.val,congrArg Subtype.val a.property⟩
  have hi : Function.Injective enc := by
    intro a b h
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : {a // f a=v.val} => z.val) h
  convert (Fintype.card_le_of_injective enc hi).trans (hf v.val) using 1 <;> congr!

theorem label_permutation_close_card {A V : Type*} [Fintype A] [Fintype V]
    (f : A → V) (π : Equiv.Perm V) (b M : ℕ)
    (hf : ∀ v, Fintype.card {a // f a=v} ≤ M) (v : V) :
    Fintype.card {a // PermutationClose π b v (f a)} ≤ M*(2*b+1) := by
  calc
    _ ≤ Fintype.card {w // PermutationClose π b v w} * M :=
      label_predicate_card_bound f _ M hf
    _ ≤ (2*b+1)*M := Nat.mul_le_mul_right M (permutationClose_neighbour_card π b v)
    _ = _ := Nat.mul_comm _ _

theorem label_fibre_bound_reindex {A Y V : Type*} [Fintype A] [Fintype Y]
    (f : A → V) (e : Y ≃ A) (M : ℕ)
    (hf : ∀ v, Fintype.card {a // f a=v} ≤ M) :
    ∀ v, Fintype.card {y // f (e y)=v} ≤ M := by
  classical
  intro v
  let enc : {y // f (e y)=v} → {a // f a=v} := fun y => ⟨e y.val,y.property⟩
  apply (Fintype.card_le_of_injective enc ?_).trans (hf v)
  intro y z h
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val h)

end Oberwolfach
