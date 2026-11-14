module

public import Oberwolfach.LongResidualEligibility

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance dualEligibilityDecEq : DecidableEq V := Classical.decEq V

def longOrdinaryArcEligible (π:Equiv.Perm V) (d:ℕ) (e:V×V):Prop:=
  ¬PermutationClose π (3*d) e.1 e.2

theorem long_dual_ineligible_incident (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (x y:V)
    (hG:G.Adj x y) (hbad:¬(longOrdinaryArcEligible π d (x,y) ∧ longMarkedArcEligible π d (x,y))):
    (longPreparationIneligibleGraph G π d).Adj x y:=by
  by_cases ho:longOrdinaryArcEligible π d (x,y)
  · exact long_marked_ineligible_incident G π d x y hG (fun hm=>hbad ⟨ho,hm⟩)
  · exact ⟨hG,Or.inl (Classical.not_not.mp ho)⟩
end Oberwolfach
