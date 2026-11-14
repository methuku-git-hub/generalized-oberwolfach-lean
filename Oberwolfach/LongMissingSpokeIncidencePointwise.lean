module

public import Oberwolfach.LongResidualMissingFromMatching

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMissingPointwiseFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_missing_spoke_in_vertex_incidence
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:U)
      (a:Fin n) (ha:rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true) (j:ℕ) (hj:j<d),
    let v:=(π^j) a
    let Marked:=longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w
    j∉packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w a →
    ∃z∈longRawIncidenceSet S (.inr (true,.inl v))\M.biUnion Q, z.1=Sum.inr (true,v,w):=by
  intro R T S hST q Q M w a ha j hj v Marked hnot
  have hvstate:rawMarkedPairSpokes π d raw true true true v w:=by
    change rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,w)=some (Sum.inl true)
    change rawIntervalState π d (fun e=>raw (Sum.inr (w,e))) v=some (Sum.inl true)
    apply (rawIntervalState_interval_iff π d (fun e=>raw (Sum.inr (w,e))) v true).2
    refine ⟨a,ha,?_⟩
    apply (permutationWindow_mem_iff π 0 (d-1) a v).mpr
    refine ⟨⟨j,by omega⟩,?_⟩
    simp [v]
  let zval:LongRawHubResource n U:=Sum.inr (true,v,w)
  have hzT:zval∈T:=by simp [T,zval,longRawHubState,typedMarkedResourceState,bernoulliVertexSet,hvstate]
  have hzS:zval∈S:=long_raw_surviving_sample_spoke P π d raw true true Del zval hzT ⟨v,w,rfl⟩
  let z:{z // z∈S}:=⟨zval,hzS⟩
  have hzInc:z∈longRawIncidenceSet S (.inr (true,.inl v)):=by
    simp only [longRawIncidenceSet,Finset.mem_filter,Finset.mem_univ,true_and]
    simp [longRawResourceIncident,z,zval]
  have hzUnmatched:z∉M.biUnion Q:=by
    intro hzM
    let emb:=survivingResourceEmbedding S T hST
    let zT:{z // z∈T}:=emb z
    have hLift:=surviving_candidate_covered_resources_lift R S T hST M
    have hzT':zT∈(M.map q).biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈T))):=by
      rw [hLift]
      exact Finset.mem_map.mpr ⟨z,hzM,rfl⟩
    have hW:=long_matched_true_spoke_covered_at_hub P π d m ℓ raw (M.map q) v w zT
      (by rfl) hzT'
    have hjpos:j∈packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w a:=by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hj,hW⟩
    exact hnot hjpos
  exact ⟨z,Finset.mem_sdiff.mpr ⟨hzInc,hzUnmatched⟩,rfl⟩
end Oberwolfach
