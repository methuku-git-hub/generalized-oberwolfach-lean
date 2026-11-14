module

public import Oberwolfach.LongDualResidualEligibility
public import Oberwolfach.RawMixedPhysicalArcHost

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance usedMixedEligibilityDecEq : DecidableEq V := Classical.decEq V

theorem long_raw_mixed_arc_type_eligible
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color) (x y:V)
    (h:rawMixedPhysicalArc G π d raw x y):
    longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y):=by
  rcases h with h|h
  · left
    exact ((markedPhysicalRim_eq_one_iff G π (3*d) _ false x y).mp h).1
  · right
    exact ((markedPhysicalRim_eq_one_iff G π (3*d) _ true x (π.symm y)).mp h).1

theorem long_used_arc_eligible_from_mixed_orientation
    (G S Used Del:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:∀x y,rawMixedPhysicalArc G π d raw x y→¬Del.Adj x y→M x y=1)
    (havoid:∀x y,Used.Adj x y→¬Del.Adj x y)
    (hdir:∀x y,Used.Adj x y→ rawMixedPhysicalArc G π d raw x y ∨ rawMixedPhysicalArc G π d raw y x):
    ∀x y,M x y=1→Used.Adj x y→longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y):=by
  intro x y hM hU
  have hD:=havoid x y hU
  rcases hdir x y hU with h|h
  · exact long_raw_mixed_arc_type_eligible G π d raw x y h
  · have hM':M y x=1:=hcorrect y x h (fun hDel=>hD hDel.symm)
    have hh:=hphysical x y
    split_ifs at hh <;> omega
end Oberwolfach
