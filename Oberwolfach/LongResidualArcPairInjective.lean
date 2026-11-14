module

public import Oberwolfach.LongDualResidualRawEncoding

@[expose] public section
/-! Ordinary and marked residual identifiers are determined by their
ordered endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_arc_pair_injective
    {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (S Small:SimpleGraph V) (M:V→V→ℕ) (π:Equiv.Perm V):
    let P:=longEligibleResidualArc M Small ⊥;
    ∀T:Finset {e:V×V // P e},
    Function.Injective (fun e:residualOrdinaryArc P T=>(e.val.val.1,e.val.val.2)) ∧
    Function.Injective (fun e:residualMarkedArc P T=>(e.val.val.1,π.symm e.val.val.2)):=by
  intro P T
  constructor
  · intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · intro a b h
    have hh:(a.val.val.1,π.symm a.val.val.2)=(b.val.val.1,π.symm b.val.val.2):=h
    have hx:=congrArg (fun p:V×V=>p.1) hh
    have hy:=congrArg (fun p:V×V=>p.2) hh
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hx (π.symm.injective hy)
end Oberwolfach
