module

public import Oberwolfach.LongPreparationIneligibleGraph
public import Oberwolfach.LongMarkedResidualIncomingChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance residualEligibilityDecEq : DecidableEq V := Classical.decEq V

def longOrdinaryIneligibleGraph (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ):SimpleGraph V where
  Adj x y:=G.Adj x y ∧ PermutationClose π (3*d) x y
  symm:=⟨by intro x y h;exact ⟨h.1.symm,(permutationClose_symm π (3*d) x y).mp h.2⟩⟩
  loopless:=⟨by intro x h;exact G.loopless.irrefl x h.1⟩

def longMarkedArcEligible (π:Equiv.Perm V) (d:ℕ) (e:V×V):Prop:=
  ¬PermutationClose π (3*d) e.1 (π.symm e.2)

theorem long_ordinary_ineligible_le_all (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ):
    longOrdinaryIneligibleGraph G π d≤longPreparationIneligibleGraph G π d:=by
  intro x y h
  exact ⟨h.1,Or.inl h.2⟩

theorem long_marked_ineligible_incident (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (x y:V)
    (hG:G.Adj x y) (hbad:¬longMarkedArcEligible π d (x,y)):
    (longPreparationIneligibleGraph G π d).Adj x y:=by
  exact ⟨hG,Or.inr (Or.inl (Classical.not_not.mp hbad))⟩
end Oberwolfach
