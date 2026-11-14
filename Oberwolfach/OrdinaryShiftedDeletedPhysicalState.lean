module

public import Oberwolfach.OrdinaryShiftedRimDeletion
public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber

@[expose] public section
/-! Deleting physical rim edges filters exactly their typed representatives
in the ordinary sample; spokes keep their original states. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def ordinaryPhysicalRimSurvives (F:Finset (Sym2 V)) (z:Sym2 V⊕(V×U)):Prop :=
  match z with
  | Sum.inl e=>e∉F
  | Sum.inr _=>True

theorem ordinary_shifted_deleted_physical_state
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color) (F:Finset (Sym2 V)):
    typedMarkedResourceState (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims raw F))
      (rawMarkedPairSpokes π d (rawMarkedDeleteRims raw F) g j)=
    fun z=>typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j) z &&
      decide (ordinaryPhysicalRimSurvives F (ordinaryMixedPhysicalResource π z)) :=by
  funext z
  apply Bool.eq_iff_iff.mpr
  cases z with
  | inl a=>
    simp [typedMarkedResourceState,ordinary_shifted_delete_rims,ordinaryMixedPhysicalResource,ordinaryPhysicalRimSurvives]
  | inr a=>
    obtain ⟨b,v,u⟩:=a
    simp [typedMarkedResourceState,ordinaryMixedPhysicalResource,ordinaryPhysicalRimSurvives,rawMarkedDeleteRims_spokes]
end Oberwolfach
