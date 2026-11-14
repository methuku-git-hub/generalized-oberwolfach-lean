module

public import Oberwolfach.LongEligibleMarkedRimAvoidsSmall
public import Oberwolfach.MarkedPartitionedResidualHost

@[expose] public section
/-! The full corrected residual, in both types, avoids the packed graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance dualRimAvoidOrdinaryFintype {V:Type} [Fintype V] (P:V×V→Prop)
    (T:Finset {a:V×V // P a}):Fintype (residualOrdinaryArc P T):=by
  unfold residualOrdinaryArc
  exact Fintype.ofFinite _
local instance dualRimAvoidMarkedFintype {V:Type} [Fintype V] (P:V×V→Prop)
    (T:Finset {a:V×V // P a}):Fintype (residualMarkedArc P T):=by
  unfold residualMarkedArc
  exact Fintype.ofFinite _

theorem long_dual_residual_rim_avoids_small
    {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (Small:SimpleGraph V) (M:V→V→ℕ) (π:Equiv.Perm V)
    (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a}):
    ∀x y,Small.Adj x y→({x,y}:Finset V)∉markedPhysicalRimSet
      (fun e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1)
      (fun e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.2)
      (fun e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1)
      (fun e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>π.symm e.val.val.2) π:=by
  apply long_eligible_marked_rim_avoids_small M Small _ _ _ _ π
  · intro e
    exact e.val.property
  · intro e
    simpa only [Equiv.apply_symm_apply] using e.val.property
end Oberwolfach
