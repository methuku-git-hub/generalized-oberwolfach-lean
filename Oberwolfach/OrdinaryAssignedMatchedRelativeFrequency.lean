module

public import Oberwolfach.OrdinaryAssignedMatchedHubCount
public import Oberwolfach.PhysicalMatchingRelativeFrequency
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Relative accuracy of a retained test's sampled weight becomes the
same frequency estimate for the number of selected wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_matched_relative_frequency
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (i₀:Fin K) (rsv θ:ℝ)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:∀i,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)) i→
        Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (w:∀i,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)) i→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources R) state)) (ε γ:ℝ) (hγ:0≤γ):
    let hub:=ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent
    let f:=ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1
    let mass:=∑x:PhysicalSampledCandidate (mixedCandidateResources R) state,
      ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val*mixedCandidateWeight w x.val
    let count:ℝ:=(L.filter (fun x=>x.val.1=some z.val.1 ∧ hub x.val.1 x.val.2=z.val.2)).card;
    |((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*mass-(1-θ)*f*n|≤ε*f*n→
    (1-γ)*mass≤∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val→
    (∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val)≤(1+γ)*mass→
    |((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*count-(1-θ)*f*n|≤(ε+γ*(1-θ+ε))*f*n :=by
  intro hub f mass count hdev hlo hhi
  have hcount:=ordinary_assigned_matched_hub_count F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent R state z L
  dsimp only at hcount
  rw [hcount] at hlo hhi
  exact physical_matching_relative_frequency _ mass count f n θ ε γ (by positivity) hγ hdev hlo hhi
end Oberwolfach
