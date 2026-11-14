module

public import Oberwolfach.LongAssignedHubTestManuscriptMargin
public import Oberwolfach.LongAssignedHubTestMargin
public import Oberwolfach.MixedHubIndicatorTest
public import Oberwolfach.MixedRestrictedHubMass
public import Oberwolfach.RestrictedSampledRootLoads
public import Oberwolfach.LongHubCountLower

@[expose] public section
/-! The root-omitted sample estimates and raw hub-count estimates imply
the matching-test mass bound without replacing the sample or weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U V I:Type} [Fintype U] [Fintype V] [Fintype I] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem long_assigned_hub_test_manuscript_mass_from_sampled_patterns
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (hK:0<K) (θ:ℝ) (hθ0:0<θ) (hθ:θ≤1/10)
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (R:∀j,E j→Finset V) (state:V→Bool) (w:∀j,E j→ℝ) (hub:∀j,E j→U)
    (i:Fin K) (j:I) (u:U) (S:Finset V) (r:ℕ) (hr:0<r) (rmax:ℝ) (hrmax:(r:ℝ)≤rmax)
    (hf:θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u)
    (hS:∀c,(R j c∩S).card=if hub j c=u then r else 0)
    (τ t countErr:ℝ) (hτ:τ≤1/16)
    (ht:t≤(longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u)/16)
    (hdeg:∀v∈S,state v=true→
      |resourcePatternLoad (R j) (w j) (fun _ _=>true) v state-
        longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u|≤
        t+τ*(longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u))
    (hcount:|((S.filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr)
    (hcountErr:countErr≤longAssignedApproxOrdinaryWeight F hF K m θ u*n/16):
    let e: {v:V // v∈bernoulliVertexSet state}↪V := Function.Embedding.subtype _
    θ*(n:ℝ)/(200*(K:ℝ)*rmax)≤
      ∑c:RestrictedResource (mixedCandidateResources R) e,
        mixedHubIndicator hub j u c.val.1 c.val.2*mixedCandidateWeight w c.val :=by
  intro e
  have hdeg':∀v∈restrictedResourceSubset e S,
      |hypergraphWeightedDegree (restrictedResourceSet (R j) e) (fun c=>w j c.val) v-
        longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u|≤
        t+τ*(longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u):=by
    intro v hv
    rw [sampled_resource_degree_eq_pattern]
    have hvS:v.val∈S:=(Finset.mem_filter.mp hv).2
    have hvstate:state v.val=true:=(mem_bernoulliVertexSet state v.val).mp v.property
    exact hdeg v.val hvS hvstate
  have heq:((restrictedResourceSubset e S).card:ℝ)=((S.filter (fun v=>state v=true)).card:ℝ):=by
    have himage:(restrictedResourceSubset e S).image e = S.filter (fun v=>state v=true):=by
      ext x
      constructor
      · intro hx
        obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,(mem_bernoulliVertexSet state v.val).mp v.property⟩
      · intro hx
        obtain ⟨hxS,hxstate⟩:=Finset.mem_filter.mp hx
        let v:{v:V // v∈bernoulliVertexSet state}:=⟨x,(mem_bernoulliVertexSet state x).mpr hxstate⟩
        exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxS⟩,rfl⟩
    rw [←himage,Finset.card_image_of_injective _ e.injective]
  have hc:(15/16:ℝ)*longAssignedApproxOrdinaryWeight F hF K m θ u*n≤
      ((restrictedResourceSubset e S).card:ℝ):=by
    rw [heq]
    have hh : -countErr≤((S.filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n:=(abs_le.mp hcount).1
    linarith
  let η:=longAssignedKeptOrdinaryContribution F hF K θ i u/longAssignedApproxOrdinaryWeight F hF K m θ u
  have hdeglo:∀v∈restrictedResourceSubset e S,(1-τ)*η-t≤
      hypergraphWeightedDegree (restrictedResourceSet (R j) e) (fun c=>w j c.val) v:=by
    intro v hv
    have hh:=(abs_le.mp (hdeg' v hv)).1
    linarith
  have hmass:=mixed_restricted_hub_test_mass_lower R e w j (mixedHubIndicator hub j u) (hub j) u S r hr
    (mixed_hub_indicator_other_family hub j u) (mixed_hub_indicator_same_family hub j u) hS ((1-τ)*η-t) hdeglo
  exact long_assigned_retained_hub_test_manuscript_mass hn F hF K m hK θ hθ0 hθ hb i u hf τ t
    (restrictedResourceSubset e S).card r rmax _ hτ ht hc (by exact_mod_cast hr) hrmax hmass
end Oberwolfach
