module

public import Oberwolfach.OrdinaryAssignedRetainedHubTests
public import Oberwolfach.PhysicalSampledCandidateRestriction

@[expose] public section
/-! The retained hub-test sum is the number of selected wheels in that
family at that hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_matched_hub_count
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (i₀:Fin K) (rsv θ:ℝ)
    (π:Equiv.Perm (Fin n)) (b m:ℕ) (f:Fin K→ℕ)
    (R:∀i,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π b (f i+2)) i→
        Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources R) state)):
    let hub:=ordinaryMixedGenericWheelHub (U:=U) π b m f;
    (∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π b m f z x.val)=
      ((L.filter (fun x=>x.val.1=some z.val.1 ∧ hub x.val.1 x.val.2=z.val.2)).card:ℝ) :=by
  intro hub
  exact mixed_hub_indicator_sum_is_card (fun x=>x.val) hub (some z.val.1) z.val.2 L
end Oberwolfach
