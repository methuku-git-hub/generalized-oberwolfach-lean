module

public import Oberwolfach.OrdinaryMatchingRetainedMassUpper
public import Oberwolfach.OrdinaryPositiveMatchingRetained
public import Oberwolfach.OrdinaryAssignedKeptSupport
public import Oberwolfach.OrdinaryAssignedMatchedRelativeFrequency

@[expose] public section
/-! The retained tests kept by the physical matching bound its actual selected
short-cycle mass on that same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_matching_retained_mass_upper
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (c D:ℝ) (P:SimpleGraph (Fin n))
    (weights:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (ε γ:ℝ) (hγ:0≤γ):
    let w:=ordinaryMixedGenericWeight wM (ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d weights)
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let mass:=fun z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ=>
      ∑x:PhysicalSampledCandidate (mixedCandidateResources R) state,
        ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val*mixedCandidateWeight w x.val;
    (∀x∈L,0<mixedCandidateWeight w x.val)→
    (∀z,|((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*mass z-
      (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n|≤
      ε*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n)→
    (∀z,(1-γ)*mass z≤∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val)→
    (∀z,(∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val)≤(1+γ)*mass z)→
    ∀u,((∑a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)):ℝ)≤
      (1-θ+(ε+γ*(1-θ+ε)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i):=by
  intro w R mass hsupp hdev hlo hhi u
  have hret:=ordinary_positive_matching_retained F hF i₀ rsv θ c D P π d m weights wM R state L hsupp
  exact ordinary_matching_retained_mass_upper F hF i₀ rsv θ π d m RM w state L ε γ hγ hret hdev hlo hhi u
end Oberwolfach
