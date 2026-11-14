module

public import Oberwolfach.RegularCycleIsomorphism

@[expose] public section
/-! Glue permutations on the fibers of a map into one permutation preserving
all fibers. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def fiberwisePermutation {X C:Type*} (f:X→C) (π:∀c:C,Equiv.Perm {x // f x=c}):Equiv.Perm X :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight π).trans (Equiv.sigmaFiberEquiv f))

theorem fiberwise_permutation_apply {X C:Type*} (f:X→C)
    (π:∀c:C,Equiv.Perm {x // f x=c}) (x:X):
    fiberwisePermutation f π x=(π (f x) ⟨x,rfl⟩).val:=by
  rfl

theorem fiberwise_permutation_preserves {X C:Type*} (f:X→C)
    (π:∀c:C,Equiv.Perm {x // f x=c}) (x:X):
    f (fiberwisePermutation f π x)=f x:=by
  rw [fiberwise_permutation_apply]
  exact (π (f x) ⟨x,rfl⟩).property
end Oberwolfach
