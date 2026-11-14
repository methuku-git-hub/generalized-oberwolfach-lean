module

public import Oberwolfach.LongPreparationPhysicalContainment
public import Oberwolfach.MarkedInnerSelectedSampleAgreement

@[expose] public section
/-! Physical state agreement on the fixed inner set supplies the selected
sample identification needed by the required-edge containment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_selected_sample_from_inner_physical_agreement
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (τ:RawMarkedOutcome V U Γ Color)
    (hAgree:∀x∈I,∀y∈I,rawExpandedMarkedCollapse (Sum.inl s(x,y)) (σ (Sum.inl s(x,y)))=τ (Sum.inl s(x,y))):
    ∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→
      (markedSampleArcSetGraph P π d τ Finset.univ).Adj x y:=by
  exact marked_inner_full_selected_sample_agreement P π d I (fun e=>rawExpandedMarkedCollapse e (σ e)) τ hAgree

theorem long_required_canonical_physical_containment
    (P Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D M:V→V→Prop)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (τ:RawMarkedOutcome V U Γ Color)
    (hAgree:∀x∈I,∀y∈I,rawExpandedMarkedCollapse (Sum.inl s(x,y)) (σ (Sum.inl s(x,y)))=τ (Sum.inl s(x,y))):
    longRequiredPhysicalGraph P (longPhysicalStateGraph P σ {0,1,2,3,4}\Used)
        (markedSampleArcSetGraph P π d τ Finset.univ) π d I D M≤
      (spanningRestriction (longPhysicalStateGraph P σ {4}) I ⊔
       spanningRestriction (longPhysicalStateGraph P σ {2,3}\Used) I) ⊔
       longPreparationIneligibleGraph P π d:=by
  apply long_required_physical_containment P _ _ Used π d I D M σ le_rfl
  exact long_selected_sample_from_inner_physical_agreement P π d I σ τ hAgree
end Oberwolfach
