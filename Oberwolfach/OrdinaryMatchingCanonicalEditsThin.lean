module

public import Oberwolfach.OrdinaryMatchingComplementTargetFromPacks
public import Oberwolfach.OrdinaryCanonicalEditedTargetRelations

@[expose] public section
/-! Instantiate the target host using exactly the edges lost from the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryCanonicalTargetThinFin (n:ℕ):DecidableEq (Fin n):=ordinaryMatchingPackedTargetFin n

theorem ordinary_matching_sampled_complement_target_from_canonical_edits
    (δ:ℝ) (hδ:0<δ):
    ∃m₀:ℕ,7≤m₀ ∧ ∀m≥m₀,∀d:ℕ,1≤d→∀θ:ℝ,0<θ→∀err:ℝ,0<err→
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e);
    ∀(t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (ζ matchErr κ:ℝ)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(Cres u)),Fintype.card c.val=i₀.val+1)
    (hres:∀u,((i₀.val+1:ℕ):ℝ)*(Cres u).card=rsv*n)
    (hcounts:∀u (g:Bool),|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop),
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀u,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀u a,(W u a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W u a).2.val=u),
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=fun u=>physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)))
    let A:=fun u=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret u
    let B:=fun u=>{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true}
    let S:=fun u=>{x:Fin n | (F u).connectedComponentMk x∉Cres u}
    let J:=fun u=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let X:=fun u=>↥(S u);
    ∀(a:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) ((F u).induce (S u))),
      (∀u,(a u).c=m+1)→(∀u,(a u).d=d)→(∀u,(a u).s₁=firstSumIndices)→
      (∀u,(a u).s₂=secondSumIndices)→(∀u,(a u).t=Finset.univ)→
      (∀u,(a u).Cembed=(a u).t.biUnion (fun j=>((a u).C j).support.toFinset))→
      (∀u j,((a u).C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)→
      (∀u (i:B u),(a u).T (.inr i)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π (H false) (H true) (Finset.univ.image (W u)) u i.val)→
      (∀u,(1-θ-matchErr)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
        ((∑j:J u,(longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)):ℝ))→
      (∀u,(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)≤1/8)→
      0≤ζ→0≤matchErr→
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤err/2→
      (∀u,((Row u\L.biUnion Q).card:ℝ)≤κ*n)→
      2*θ+err+((m:ℝ)+2)*κ≤δ→
      ∀errUpper:ℝ,0≤errUpper→errUpper≤θ/8→
      (∀u,((∑j:J u,(longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)):ℝ)≤
        (1-θ+errUpper)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i))→
      ∀(αCap b:ℝ),0<αCap→0≤b→16/(d:ℝ)+16*κ+16*b/αCap≤θ/8→
      ∀(P Target:SimpleGraph (Fin n)),Target≤P→
      let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4}
      let G:=Target\S₀
      let Del:=S₀\Target
      let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
      let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y;
      (∀x,((Finset.univ.filter (fun y=>Xor (Target.Adj x y) (S₀.Adj x y))).card:ℝ)≤b*n)→
      OrdinaryProtectedBadEdgeAssignments π d σ αCap→b≤αCap/16→b≤δ/4→
      ∀(ext:∀u,A u⊕B u→Fin ((m+1)*d+5)↪X u)
        (inner:∀u,A u→Fin ((m+1)*d+1)↪X u),
      (∀u,IsEmpty (A u))→
      (∀u i,((a u).P i).support=List.ofFn (ext u i))→
      (∀u i k,inner u i k=ext u (.inl i) ⟨k.val+2,by omega⟩)→
      ∀(Old:∀u,Finset (X u)),
      (∀u,Old u=(a u).oldDomain\bufferedPathStrictInterior (fun _:A u=>(m+1)*d) (inner u))→
      ∀(ψ:∀u,X u→Fin n),
      (∀u i (j:Fin (d+1)),bufferedMarker (m+1) d (ext u i) j∈(a u).prescribed→
        ψ u (bufferedMarker (m+1) d (ext u i) j)=
          (π^j.val) (retainedAndRawIntervalRoot π d (fun e=>σ (Sum.inr e)) false true t Jret u i))→
      (∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))→
      (∀u,Disjoint ((Old u).image (ψ u))
        (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u))→
      ∀(Host:SimpleGraph (Fin n)),Host≤P→
      (∀u,ActualOldImageDirected (a u) (ψ u) (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims raw Del.edgeFinset)))→
      ∀(Pack:U→Finset (Finset (Fin n))),
      (∀u,ActualOldPhysicalCoverage (a u) (ψ u) (Pack u))→
      (∀u v,u≠v→Disjoint (Pack u) (Pack v))→
      ∀β:ℝ,0<β→β≤1→δ≤(β/100)^2→100/β≤(n:ℝ)→2/Real.sqrt δ≤(n:ℝ)→Fintype.card U≤n→
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>σ (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/((m:ℝ)+1)+4*(n:ℝ)^(3/4:ℝ))→
      (∀Del':SimpleGraph (Fin n),(∀v,(Del'.degree v:ℝ)≤b*n)→∀u,
        IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del'.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) β)→
    ∃(D:∀u,X u→X u→Prop) (pieces:∀u,List (PrescribedSourcePiece {x // x∈(a u).remaining}))
      (M:U→Finset (Fin n×Fin n))
      (B:∀u,Finset {x // x∈(a u).remaining})
      (g Φ:∀u,{x // x∈(a u).remaining}→Fin n) (f:∀u,X u↪Fin n),
      (∀u,prescribedDependentGraph pieces u=((a u).graph).induce (fun x=>x∈(a u).remaining)) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y ↔ D u x.1 y.1 ∧ (a u).graph.Adj x.1 y.1) ∧
      (∀u,IsPrescribedOrientedMatching (M u)) ∧
      (∀u,Disjoint ((Old u).image (ψ u)) (prescribedMatchingEndpoints (M u))) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) ∧
      (∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset) ∧
      (∀u,Function.Injective (Φ u)) ∧
      (∀u,residualSubtypeSet (a u).remaining (a u).prescribed⊆B u ∧
        (∀x∈residualSubtypeSet (a u).remaining (a u).prescribed,g u x=ψ u x.1) ∧
        (B u).image (g u)=
          (residualSubtypeSet (a u).remaining (a u).prescribed).image (fun x=>ψ u x.1)∪
            prescribedMatchingEndpoints (M u) ∧
        (prescribedInducedArcs (prescribedDependentDigraph pieces u) (B u)).image (Prod.map (g u) (g u))=M u) ∧
      (∀u x,x∈B u→Φ u x=g u x) ∧
      (∀u x,x∉B u→Φ u x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) ∧
      (∀u x y,prescribedDependentDigraph pieces u x y→Dstar (Φ u x) (Φ u y) ∧
        ((x∉B u ∨ y∉B u)→Dfree (Φ u x) (Φ u y))) ∧
      let E:U→Finset (Sym2 (Fin n)):=fun u=>((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u));
      PairwisePhysicalDisjoint E ∧ (∀u,(M u).image prescribedArcPhysical⊆E u) ∧
      (∀e∈G.edgeFinset,∃u,e∈E u) ∧
      (∀u,Disjoint (E u\(M u).image prescribedArcPhysical) G.edgeFinset) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*n) ∧
      (∀u x,x∈(a u).oldDomain→f u x=ψ u x) ∧
      (∀u (x:{x // x∈(a u).remaining}),f u x.1=Φ u x) ∧
      (∀u,(((F u).induce (S u)).edgeFinset).image (Sym2.map (f u))=
        (a u).deletedEdges.image (Sym2.map (ψ u)) ∪
          (((a u).graph.induce (fun x=>x∈(a u).remaining)).edgeFinset).image (Sym2.map (Φ u))) ∧
      (∀u x y,((F u).induce (S u)).Adj x y→Target.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) ((F u).induce (S u)) (f u))
        (partialFactorPhysicalEdgesPoly (X v) ((F v).induce (S v)) (f v)))   :=by
  obtain ⟨m₀,hm₀,hMain⟩:=ordinary_matching_sampled_complement_target_from_packs δ hδ
  refine ⟨m₀,hm₀,?_⟩
  intro m hm d hd θ hθ err herr
  obtain ⟨N,hN⟩:=hMain m hm d hd θ hθ err herr
  refine ⟨N,?_⟩
  intro n K hnN U _ _ hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hrsclass hclass π hnoshort σ raw t Jret ζ matchErr κ hgood Cres hsize hres hcounts Rim
    H RM state RR φ L W hW Q Row A B S J X a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch hQ hζ he hrate hrow hbudget errUpper herrUpper0 herrUpper hmatchUpper αCap b hα hb hbudgetCap P Target hTarget S₀ G Del Dfree Dstar hedit hEvent hbsmall hbδ ext inner hempty hsupp hinner Old hOldEq ψ hmarker hψ hOld Host hHP hdir Pack hcoverOld hPackDis β hβ hβ1 hδbound hnβ hn' hU hOcc hLists
  have hset:(letI:DecidableEq (Fin 6):=instDecidableEqFin 6; ({0,1,2,3,4}:Finset (Fin 6)))=
      (letI:DecidableEq (Fin 6):=ordinaryCanonicalTargetThinFin 6; ({0,1,2,3,4}:Finset (Fin 6))):=by
    ext x
    simp
  have hedit₀:∀x,((Finset.univ.filter (fun y=>Xor (Target.Adj x y)
      ((longPhysicalStateGraph P σ (letI:DecidableEq (Fin 6):=instDecidableEqFin 6; ({0,1,2,3,4}:Finset (Fin 6)))).Adj x y))).card:ℝ)≤b*n:=by
    rw [hset]
    exact hedit
  have hrels:=ordinary_canonical_edited_target_relations P Target Host hTarget hHP π d σ (b*n) hedit₀
  dsimp only at hrels
  rw [hset] at hrels
  obtain ⟨hDelDegree,hdegree,hOldTarget,hDstar,hDD,hstar,hselected⟩:=hrels
  have hJ:∀v,(G.degree v:ℝ)≤δ*n:=by
    intro v
    have hh:=hdegree v
    have hm:=mul_le_mul_of_nonneg_right hbδ (show 0≤(n:ℝ) by positivity)
    nlinarith
  have hext:∀u,IsExtendingList Dfree
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) β:=by
    apply hLists Del
    intro v
    have hh:=hDelDegree v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hEdge:(letI:DecidableRel G.Adj:=fun x y=>Classical.propDecidable (G.Adj x y); G.edgeFinset)=G.edgeFinset:=by
    exact graph_edge_finset_instance_eq G _ _
  have hResult:=hN (n:=n) (K:=K) hnN (U:=U) hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hrsclass hclass π hnoshort σ t Jret ζ matchErr κ hgood Cres hsize hres hcounts Rim L W hW a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch hQ hζ he hrate hrow hbudget errUpper herrUpper0 herrUpper hmatchUpper αCap b hα hb hbudgetCap P Target G G rfl hedit hEvent hbsmall hbδ Dstar Dfree hDstar hDD ext inner hempty hsupp hinner Old hOldEq ψ hmarker hψ hOld Host Del hHP (by
      intro x y h
      apply hOldTarget x y
      convert h using 1 <;> congr 3 <;> exact Subsingleton.elim _ _) hstar hselected (by
      intro u
      have hh:=hdir u
      convert hh using 1 <;> congr 4 <;> exact Subsingleton.elim _ _) Pack hcoverOld hPackDis β hβ hβ1 hδbound hnβ hn' hU hOcc (by
      intro v
      have hh:=hJ v
      convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _) hext
  obtain ⟨D, pieces, M, Bout, g, Φ, f, hgraph, harcs, hM, hOldM, hMlist,
    hMsub, hinj, hB, hΦg, hΦL, hΦarc, hEpair, hME, hcover, havoid,
    hdeg, hfold, hfnew, hpartition, hhost, hdisjoint⟩ := hResult
  refine ⟨D, pieces, M, Bout, g, Φ, f, hgraph, harcs, hM, hOldM, hMlist,
    ?_, hinj, hB, hΦg, hΦL, hΦarc, hEpair, hME, ?_, ?_, hdeg, hfold,
    hfnew, hpartition, hhost, hdisjoint⟩
  · intro u
    have hh := hMsub u
    convert hh using 1 <;> congr 4 <;> exact Subsingleton.elim _ _
  · intro e he
    apply hcover e
    convert he using 1 <;> congr 4 <;> exact Subsingleton.elim _ _
  · intro u
    have hh := havoid u
    convert hh using 1 <;> congr 4 <;> exact Subsingleton.elim _ _
end Oberwolfach
