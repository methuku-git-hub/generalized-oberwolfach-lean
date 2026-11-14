module

public import Oberwolfach.LongActualPrescribedMatchingBound
public import Oberwolfach.PrescribedBoundaryMatchingLoadBudget

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longActualPrescribedLoadFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_prescribed_load_from_matching_and_boundary
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m c:ℕ) (hd:1≤d) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n)))
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) {J:U→Type} [∀w,DecidableEq (J w)]
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})
      (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n)
    (hc:∀w,(data w).c=c) (hdd:∀w,(data w).d=d)
    (hs₂:∀w,(data w).s₂=secondSumIndices)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i))
    (hT:∀w i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
      (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w
      (retainedAndRawIntervalRoot π d σ false true t Jret w i))
    (H:Finset U) (A:Finset (Fin n)) (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hboundary:∀v∈A,((rawIntervalBoundaryHubSet π d σ H v).card:ℝ)≤4*(H.card:ℝ)/d+4*(A.card:ℝ)^(3/4:ℝ))
    (Kbad:SimpleGraph (Fin n)) (Z:U→Finset (Fin n)) (δ:ℝ)
    (hH:(H.card:ℝ)≤(A.card:ℝ)) (hD:4/(d:ℝ)≤δ/8)
    (hN:4*(A.card:ℝ)^(3/4:ℝ)≤δ*(A.card:ℝ)/8)
    (hMatching:2*(max a γ*n)≤δ*(A.card:ℝ)/4)
    (hbad:∀v∈A,(Kbad.degree v:ℝ)≤δ*(A.card:ℝ)/4)
    (htargets:∀v∈A,((H.filter (fun w=>v∈Z w)).card:ℝ)≤δ*(A.card:ℝ)/4),
    ∀v∈A,((H.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((H.filter (fun w=>v∈Z w)).card:ℝ)≤δ*(A.card:ℝ):=by
  intro σ R T S hST q Q M F J _ data ext ψ hc hdd hs₂ hsupp hmarker hT H A a γ hγ hu hmatch hboundary Kbad Z δ hH hD hN hMatching hbad htargets v hv
  have hpres:=long_actual_prescribed_from_matching_and_boundary P π d m c hd ℓ raw Del t Jret M F data ext ψ hc hdd hs₂ hsupp hmarker hT H A a γ hγ hu hmatch hboundary v hv
  exact prescribed_boundary_matching_load_budget A.card H.card d δ a γ n (by exact_mod_cast hd) hH hD hN hMatching _ _ _ hpres (hbad v hv) (htargets v hv)
end Oberwolfach
