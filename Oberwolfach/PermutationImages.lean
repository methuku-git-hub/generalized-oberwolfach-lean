module

public import Oberwolfach.FiniteLawComposition
public import Oberwolfach.FixedPartitions
public import Oberwolfach.OrderedSamples
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-! The images of a fixed injection under a uniform permutation form a
uniform injection. This includes joint placement of prescribed labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def permutationInverseEquiv (V : Type*) : Equiv.Perm V ≃ Equiv.Perm V where
  toFun := Equiv.symm
  invFun := Equiv.symm
  left_inv _ := rfl
  right_inv _ := rfl

theorem uniformPermutation_images {I V : Type*} [Fintype I] [Fintype V]
    (x : I ↪ V) [Nonempty (I ↪ V)] :
    (FiniteLaw.uniform (Equiv.Perm V)).map (fun σ => x.trans σ.toEmbedding) =
      FiniteLaw.uniform (I ↪ V) := by
  apply finiteLaw_uniform_map_transitive
  intro f g
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  refine ⟨permutationRightEquiv e, ?_⟩
  intro σ
  constructor
  · intro h
    ext i
    apply e.injective
    have hi := congrArg (fun z : I ↪ V => z i) h
    exact hi.trans (he i).symm
  · intro h
    ext i
    change e (σ (x i)) = g i
    rw [show σ (x i) = f i from congrArg (fun z : I ↪ V => z i) h]
    exact he i

theorem uniformPermutation_inverse_images {I V : Type*} [Fintype I] [Fintype V]
    (x : I ↪ V) [Nonempty (I ↪ V)] :
    (FiniteLaw.uniform (Equiv.Perm V)).map (fun σ => x.trans σ.symm.toEmbedding) =
      FiniteLaw.uniform (I ↪ V) := by
  have h := uniformPermutation_images x
  rw [← finiteLaw_uniform_map_equiv (permutationInverseEquiv V)] at h
  rw [finiteLaw_map_map] at h
  convert! h using 1

end Oberwolfach
