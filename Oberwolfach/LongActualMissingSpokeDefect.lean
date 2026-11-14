module

public import Oberwolfach.LongMissingSpokeIncidencePointwise
public import Oberwolfach.RetainedAndRawIntervalGeometry
public import Oberwolfach.ActualResidualDataFromFamilies

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longActualMissingFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_missing_positions_are_spoke_defects
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n)))
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) {J:U→Type} [∀w,DecidableEq (J w)]
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:=J w) (F w)),
    (∀w,(data w).s₂=secondSumIndices) →
    (∀w i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
      (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w
      (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) →
    ∀w i,i∈(data w).s₂→∀j<d,j∉(data w).T i→
      ∃z∈longRawIncidenceSet S (.inr (true,.inl ((π^j)
        (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i))))\M.biUnion Q,
        z.1=Sum.inr (true,(π^j) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i),w):=by
  intro R T S hST q Q M F J _ data hs₂ hT w i hi j hj hnot
  rw [hs₂ w,secondSumIndices] at hi
  obtain ⟨a,ha,haeq⟩:=Finset.mem_image.mp hi
  subst i
  rw [hT w (.inr a)] at hnot
  exact long_missing_spoke_in_vertex_incidence P π d m hd ℓ raw Del M w a.val a.property j hj hnot
end Oberwolfach
