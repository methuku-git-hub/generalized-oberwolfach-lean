module

public import Oberwolfach.LongPreparationIneligibleGraph

@[expose] public section
/-! Physical separation by 3d+2 supplies all ordinary and shifted
auxiliary separation conditions for either orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_physical_far_auxiliary (π:Equiv.Perm V) (d:ℕ) (x y:V)
    (hfar:¬PermutationClose π (3*d+2) x y):
    ¬PermutationClose π (3*d) x y ∧
    ¬PermutationClose π (3*d) x (π.symm y) ∧
    ¬PermutationClose π (3*d) y (π.symm x) :=by
  constructor
  · intro h
    exact hfar (permutationClose_mono_radius π _ _ (by omega) x y h)
  constructor
  · intro h
    have hh:=permutationClose_apply_right π (3*d) x (π.symm y) h
    have hh':PermutationClose π (3*d+1) x y:=by simpa only [Equiv.apply_symm_apply] using hh
    exact hfar (permutationClose_mono_radius π _ _ (by omega) x y hh')
  · intro h
    have hh:=permutationClose_apply_right π (3*d) y (π.symm x) h
    have hh':PermutationClose π (3*d+1) y x:=by simpa only [Equiv.apply_symm_apply] using hh
    have hr:PermutationClose π (3*d+1) x y:=(permutationClose_symm π _ _ _).mp hh'
    exact hfar (permutationClose_mono_radius π _ _ (by omega) x y hr)
end Oberwolfach
