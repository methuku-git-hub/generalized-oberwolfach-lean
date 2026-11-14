module

public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section
/-! A fixed-point-free permutation has no equal adjacent orbit labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem permutation_orbit_adjacent_ne
    {V:Type*} (π:Equiv.Perm V) (hπ:∀x,π x≠x) (a:V):
    ∀i,(π^i) a≠(π^(i+1)) a:=by
  intro i h
  have hh:=hπ ((π^i) a)
  rw [pow_succ',Equiv.Perm.mul_apply] at h
  exact hh h.symm
end Oberwolfach
