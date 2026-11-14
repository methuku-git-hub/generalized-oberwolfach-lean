module

public import Oberwolfach.OrdinaryMatchingCycleMassLower
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

theorem ordinary_matching_retained_mass
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (w:∀i,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)) i→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (ε γ:ℝ) (hγ:0≤γ):
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let mass:=fun z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ=>
      ∑x:PhysicalSampledCandidate (mixedCandidateResources R) state,
        ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val*mixedCandidateWeight w x.val;
    (∀z,|((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*mass z-
      (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n|≤
      ε*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n)→
    (∀z,(1-γ)*mass z≤∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val)→
    (∀z,(∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val)≤(1+γ)*mass z)→
    ∀u,(1-θ-(ε+γ*(1-θ+ε)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
      ((∑a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)):ℝ):=by
  intro R mass hdev hlo hhi u
  have hcount:∀z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ,
      |((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*
        ((L.filter (fun x=>x.val.1=some z.val.1 ∧ ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=z.val.2)).card:ℝ)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n|≤
        (ε+γ*(1-θ+ε))*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n:=by
    intro z
    exact ordinary_assigned_matched_relative_frequency F hF i₀ rsv θ π d m R w state z L ε γ hγ (hdev z) (hlo z) (hhi z)
  have hh:=ordinary_matching_cycle_mass_lower F hF i₀ rsv θ π d m RM state L u (ε+γ*(1-θ+ε)) hcount
  dsimp only at hh
  rw [ordinary_assigned_kept_fraction_sum_retained F hF i₀ rsv θ u] at hh
  exact hh
end Oberwolfach
