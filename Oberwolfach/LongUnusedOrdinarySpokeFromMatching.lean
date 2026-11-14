module

public import Oberwolfach.LongMatchedOrdinarySpokeOldImage
public import Oberwolfach.LongUnusedSpokeIncidence
public import Oberwolfach.LongRawSurvivingResourceState

@[expose] public section
/-! The unused ordinary spokes lie among the uncovered surviving resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longUnusedOrdinarySpokes {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (old:U→Finset (Fin n)) (w:U):Finset (Fin n):=
  Finset.univ.filter (fun v=>rawMarkedPairSpokes π d raw true true false v w ∧ v∉old w)

theorem long_unused_ordinary_spokes_matching_bounds
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    let QT:=restrictedResourceSet R (Function.Embedding.subtype (·∈T))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (old:U→Finset (Fin n)),
      (∀(w:U) (a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)),
        (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2=w→
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.1.val),v∈old w)→
      (∀w W,W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w→
        ∀i:Fin (m+1),W.1.val i∈old w)→
      (∀w,(longUnusedOrdinarySpokes π d raw old w).card≤
        (longRawIncidenceSet S (.inr (false,.inr w))\M.biUnion Q).card) ∧
      (∀v,(Finset.univ.filter (fun w=>v∈longUnusedOrdinarySpokes π d raw old w)).card≤
        (longRawIncidenceSet S (.inr (false,.inl v))\M.biUnion Q).card):=by
  intro R T S hST q Q QT M old hOrd hMarked
  apply long_unused_spoke_incidence_bounds S (M.biUnion Q) (longUnusedOrdinarySpokes π d raw old)
  intro w v hv
  have hv':rawMarkedPairSpokes π d raw true true false v w ∧ v∉old w:=by
    simpa [longUnusedOrdinarySpokes] using hv
  have hz:Sum.inr (false,v,w)∈T:=by
    simpa [T,bernoulliVertexSet,longRawHubState,typedMarkedResourceState] using hv'.1
  have hsurv:Sum.inr (false,v,w)∈S:=by
    apply long_raw_surviving_sample_spoke P π d raw true true Del _ hz
    exact ⟨v,w,by simp [typedResourcePhysical,markedResourceTypeEquiv]⟩
  let x:S:=⟨Sum.inr (false,v,w),hsurv⟩
  refine ⟨x,rfl,?_⟩
  intro hx
  obtain ⟨c,hc,hxQ⟩:=Finset.mem_biUnion.mp hx
  let f:=survivingResourceEmbedding S T hST
  have hxT:f x∈(M.map q).biUnion QT:=by
    apply Finset.mem_biUnion.mpr
    refine ⟨q c,Finset.mem_map.mpr ⟨c,hc,rfl⟩,?_⟩
    change f x∈restrictedResourceSet R (Function.Embedding.subtype (·∈T))
      (restrictedResourceNestedLift R (Function.Embedding.subtype (·∈S))
        (Function.Embedding.subtype (·∈T)) f (fun _=>rfl) c)
    rw [restricted_resource_nested_lift_set]
    exact Finset.mem_map.mpr ⟨x,hxQ,rfl⟩
  have hOld:v∈old w:=by
    apply long_matched_ordinary_spoke_in_old_image P π d m ℓ raw (M.map q) old ?_ ?_ v w (f x) rfl ?_
    · intro u a ha z hz
      apply hOrd u a ha z
      convert hz using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
    · exact hMarked
    · convert hxT using 1 <;> congr 5 <;> exact Subsingleton.elim _ _
  exact hv'.2 hOld
end Oberwolfach
