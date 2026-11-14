module

public import Oberwolfach.FactorOrientationNoTwoCycles

@[expose] public section
/-! A consistent directed edge propagates along a cycle whenever each
source vertex has at most one incoming arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem directed_orientation_propagates_on_orbit
    {X:Type*} (σ:Equiv.Perm X) (D:X→X→Prop)
    (hcover:∀x,D x (σ x) ∨ D (σ x) x)
    (hin:∀x y z,D y x→D z x→y=z)
    (hno2:∀x,σ (σ x)≠x) (a:X) (ha:D a (σ a)):
    ∀n:ℕ,D ((σ^n) a) (σ ((σ^n) a)):=by
  intro n
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    have hnext:D (σ ((σ^n) a)) (σ (σ ((σ^n) a))) :=by
      rcases hcover (σ ((σ^n) a)) with hf | hb
      · exact hf
      · have heq:((σ^n) a)=σ (σ ((σ^n) a)):=hin (σ ((σ^n) a)) ((σ^n) a) (σ (σ ((σ^n) a))) ih hb
        exact False.elim (hno2 ((σ^n) a) heq.symm)
    simpa only [pow_succ',Equiv.Perm.mul_apply] using hnext
end Oberwolfach
