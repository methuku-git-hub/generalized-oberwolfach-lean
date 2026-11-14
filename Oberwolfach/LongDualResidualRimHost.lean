module

public import Oberwolfach.LongEligibleMarkedRimHost
public import Oberwolfach.MarkedPartitionedResidualHost

@[expose] public section
/-! The corrected ordinary/marked partition is physically contained in the
original oriented class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance dualRimHostOrdinaryFintype {V:Type} [Fintype V] (P:V×V→Prop)
    (T:Finset {a:V×V // P a}):Fintype (residualOrdinaryArc P T):=by
  unfold residualOrdinaryArc
  exact Fintype.ofFinite _
local instance dualRimHostMarkedFintype {V:Type} [Fintype V] (P:V×V→Prop)
    (T:Finset {a:V×V // P a}):Fintype (residualMarkedArc P T):=by
  unfold residualMarkedArc
  exact Fintype.ofFinite _

theorem long_dual_residual_rim_le_host
    {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (S Small:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (π:Equiv.Perm V) (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a}):
    physicalEdgeGraph (markedPhysicalRimSet
      (fun x:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>x.val.val.1)
      (fun x:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>x.val.val.2)
      (fun x:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>x.val.val.1)
      (fun x:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>π.symm x.val.val.2) π)≤S:=by
  apply long_eligible_marked_rim_le_host S Small M hphysical _ _ _ _ π
  · intro e
    exact e.val.property
  · intro e
    simpa only [Equiv.apply_symm_apply] using e.val.property
end Oberwolfach
