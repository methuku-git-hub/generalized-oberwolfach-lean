module

public import Oberwolfach.PermutationOrbitNoAdjacentRepeat

@[expose] public section
/-! The end of a selected subinterval differs from every earlier label of an
injective extended permutation interval. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_orbit_subinterval_terminal_ne
    {V:Type*} (π:Equiv.Perm V) (a:V) (d start n:ℕ) (hbound:start+n≤d)
    (hinj:Function.Injective (fun k:Fin (d+1)=>(π^k.val) a)):
    ∀ i, start ≤ i → i < start+n → (π^(start+n)) a≠(π^i) a:=by
  intro i hi hj heq
  have he:((⟨start+n,by omega⟩:Fin (d+1)))=⟨i,by omega⟩:=hinj heq
  have hv:=congrArg Fin.val he
  simp only [Fin.val_mk] at hv
  omega
end Oberwolfach
