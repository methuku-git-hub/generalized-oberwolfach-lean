module

public import Oberwolfach.FirstVortexActualOutsideImageBound
public import Oberwolfach.ActualResidualPhysicalUnionOutside
public import Oberwolfach.LongActualPrescribedAllRootsMatchingBound
public import Oberwolfach.FirstVortexRestrictedCompletionOutsideLoad
public import Oberwolfach.LongActualMissingSpokeDefect
public import Oberwolfach.LongTrueSpokeDefectFromMatching
public import Oberwolfach.ActualPrescribedFromBoundarySpokeDefects
public import Oberwolfach.ActualPrescribedMarkerImageGeometry

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexActualOutsideDegreeBoundFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_actual_outside_degree_bound
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
    let H:Finset U:=Finset.univ
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2) {J:U→Type} [∀w,DecidableEq (J w)]
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
    (boundary:ℝ) (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hboundary:∀v,((rawIntervalBoundaryHubSet π d σ H v).card:ℝ)≤boundary),
    ∀(I:Finset (Fin n)) (Kbad:SimpleGraph (Fin n)) (assign:Sym2 (Fin n)→U)
    (orient:Sym2 (Fin n)→Fin n×Fin n) (Z:U→Finset (Fin n))
    (B:∀w,Finset {x // x∈(data w).remaining}) (g Φ:∀w,{x // x∈(data w).remaining}→Fin n)
    (Qres:∀w,SimpleGraph {x // x∈(data w).remaining})
    (hQres:∀w,Qres w=((data w).graph).induce (↑(data w).remaining:Set (Fin n)))
    (hinj:∀w,Function.Injective (Φ w))
    (aScale κ lossBad:ℝ),
    (∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e)→
    (∀w x,x∈B w→Φ w x=g w x)→
    (∀w,(B w).image (g w)=(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1)∪
      prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w)∪Z w)→
    (∀w,Z w⊆I)→(∀v,(Kbad.degree v:ℝ)≤lossBad)→
    (∀v,((((Finset.univ.filter (fun z:(Σw,{x // x∈(data w).remaining})=>z.2∉B z.1)).filter
      (fun z=>z.1∈H)).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤κ*aScale+1)→
    let E:U→Finset (Sym2 (Fin n)):=fun w=>(Qres w).edgeFinset.image (Sym2.map (Φ w));
    ∀v,v∉I→((prescribedPhysicalUnion E).degree v:ℝ)≤
      2*((boundary+2*(max a γ*n))+lossBad+(κ*aScale+1)) :=by
  intro σ R T S hST q Q H M F hF J _ data ext ψ hc hdd hs₂ hsupp hmarker hT boundary a γ hγ hu hmatch hboundary
    I Kbad assign orient Z B g Φ Qres hQres hinj aScale κ lossBad hOrient hfixed hforced hZ hK hfree E v hv
  have himage:=first_vortex_actual_outside_image_bound P π d m c hd ℓ raw Del t Jret M F data ext ψ
    hc hdd hs₂ hsupp hmarker hT H boundary a γ hγ hu hmatch hboundary I Kbad assign orient Z B g Φ
    aScale κ lossBad hOrient hfixed hforced hZ hK hfree v hv
  have hload:((Finset.univ.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤
      (boundary+2*(max a γ*n))+lossBad+(κ*aScale+1):=by simpa only [H] using himage
  exact actual_residual_physical_union_degree_from_image_load F hF _ J data Qres hQres Φ hinj v _ hload
end Oberwolfach
