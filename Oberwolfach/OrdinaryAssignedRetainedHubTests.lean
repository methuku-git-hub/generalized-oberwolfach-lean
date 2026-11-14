module

public import Oberwolfach.OrdinaryAssignedRetainedCoefficient
public import Oberwolfach.OrdinaryMixedGenericFamily
public import Oberwolfach.LongMixedHubSpokeCounts
public import Oberwolfach.MixedHubIndicatorTest

@[expose] public section
/-! The ordinary matching tests are indexed by precisely the retained
factor-frequency pairs and use the actual candidate hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def OrdinaryAssignedRetainedHubTest (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (i₀:Fin K) (rsv θ:ℝ):Type :=
  {z:Fin K×U // θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.2 z.1}

instance ordinaryAssignedRetainedHubTestFintype (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (i₀:Fin K) (rsv θ:ℝ):
    Fintype (OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ):=by
  classical
  unfold OrdinaryAssignedRetainedHubTest
  infer_instance

def ordinaryMixedGenericWheelHub (π:Equiv.Perm (Fin n)) (b m:ℕ) (f:Fin K→ℕ):
    ∀j:Option (Fin K),OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π b (f i+2)) j→U
  | none,W=>W.2.val
  | some _,W=>W.2

def ordinaryAssignedRetainedHubIndicator (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (i₀:Fin K) (rsv θ:ℝ)
    (π:Equiv.Perm (Fin n)) (b m:ℕ) (f:Fin K→ℕ)
    (z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ)
    (c:Σj,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π b (f i+2)) j):ℝ :=
  mixedHubIndicator (ordinaryMixedGenericWheelHub (U:=U) π b m f) (some z.val.1) z.val.2 c.1 c.2

theorem ordinary_assigned_retained_hub_indicator_range
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (i₀:Fin K) (rsv θ:ℝ)
    (π:Equiv.Perm (Fin n)) (b m:ℕ) (f:Fin K→ℕ)
    (z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ)
    (c:Σj,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π b (f i+2)) j):
    0≤ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π b m f z c ∧
      ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π b m f z c≤1 :=by
  exact mixed_hub_indicator_nonnegative (ordinaryMixedGenericWheelHub (U:=U) π b m f)
    (some z.val.1) z.val.2 c.1 c.2

theorem ordinary_mixed_generic_hub_spoke_count
    (π:Equiv.Perm (Fin n)) (b m:ℕ) (f:Fin K→ℕ) (i:Fin K) (u:U)
    (W:OrderedOrdinaryWheel (U:=U) π b (f i+2)):
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π b (f i+2))=>orderedOrdinaryResources W);
    (R (some i) W∩ordinaryCommonHubSpokeRoots u).card=
      if ordinaryMixedGenericWheelHub (U:=U) π b m f (some i) W=u then f i+2 else 0 :=by
  intro R
  have hh:=ordered_ordinary_common_hub_spoke_count W u
  convert hh using 1 <;> (try simp only [R,ordinaryMixedGenericResources,ordinaryMixedGenericWheelHub]) <;> congr! 4
end Oberwolfach
