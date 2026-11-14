module

public import Oberwolfach.LongClassFullPackingHostGeometry
public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.LongUsedSelectedDisjoint

@[expose] public section
/-! The selected matching and the class deletion witness supply the host
orientation and reserve avoidance for the actual class-restricted repair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedFullPackingGeometryFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matched_class_full_packing_host_geometry
    {n K d r:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let T:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (Mix.map q)
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack=>longClassInnerRequiredRepair S Used Kbase I Pack
    (∀x y,rawSelectedPhysicalRelation G π d (fun e=>z.1 (Sum.inl e)) x y→¬Del.Adj x y→Mhost x y=1) ∧
    (∀Pack x y,(Kplus Pack).Adj x y→Mhost x y=1∨Mhost y x=1) ∧
    (∀Pack x y,(Kplus Pack).Adj x y→¬(markedResourceRimGraph C).Adj x y):=by
  intro raw ℓ R T Q q φ Mix Used Sel Req Kbase Kplus
  have hdis:Disjoint Sel Used:=by
    have hh:=long_used_sampled_matching_avoids_selected G π d z.1 true true
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (Mix.map q)
    convert hh using 1 <;> congr! 5 <;> exact Subsingleton.elim _ _
  have hUsed:∀x y,Used.Adj x y→¬Sel.Adj x y:=by
    intro x y hu hs
    exact (disjoint_iff_inf_le.mp hdis) ⟨hs,hu⟩
  rcases hw with ⟨hphysical,_,_,_,hcorrect,_,hdel,hfree,_,_⟩
  have hDel:∀x y,(markedResourceRimGraph C).Adj x y→¬Del.Adj x y:=by
    intro x y hr hd
    exact hdel x y hd (Or.inr hr)
  have hgeom:=long_class_full_packing_host_geometry G S Del Used (markedResourceRimGraph C) π z.1 Mhost I hphysical hcorrect hreserve hDel hUsed
  exact ⟨hfree,hgeom.1,hgeom.2⟩
end Oberwolfach
