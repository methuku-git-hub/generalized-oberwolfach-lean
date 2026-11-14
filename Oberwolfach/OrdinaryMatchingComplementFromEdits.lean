module

public import Oberwolfach.OrdinaryUnreservedFamilySizeCapacityMatching
public import Oberwolfach.OrdinaryAssignmentUnreservedSampledLoadPlacement
public import Oberwolfach.OrdinaryEmptyFinalResidualGlue
public import Oberwolfach.ResidualActualEdgePartition
public import Oberwolfach.OrdinaryEmptyFinalPhysicalCompletion
public import Oberwolfach.OrdinaryOldFamilyAvoidsSampleAdded
public import Oberwolfach.OrdinaryAddedEdgesEditDegree

@[expose] public section
/-! One physical matching, the sampled occupancy and protected assignment
jointly give simultaneous placement on all unreserved residual factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryMatchingEditComplementFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_matching_sampled_complement_embedding_from_edits
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
      ∀(P Target G Jbad:SimpleGraph (Fin n)),
      G=Target\longPhysicalStateGraph P σ {0,1,2,3,4}→
      (∀x,((Finset.univ.filter (fun y=>Xor (Target.Adj x y) ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))).card:ℝ)≤b*n)→
      OrdinaryProtectedBadEdgeAssignments π d σ αCap→b≤αCap/16→b≤δ/4→
      ∀(Dstar Dfree:Fin n→Fin n→Prop),
      (∀x y,G.Adj x y→Dstar x y∨Dstar y x)→(∀x y,Dfree x y→Dstar x y)→
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
      ∀(Host Del:SimpleGraph (Fin n)),Host≤P→
      (∀x y,Dstar x y→P.Adj x y)→
      (∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y)→
      (∀u,ActualOldImageDirected (a u) (ψ u) (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims raw Del.edgeFinset)))→
      (∀u v,u≠v→Disjoint ((a u).deletedEdges.image (Sym2.map (ψ u))) ((a v).deletedEdges.image (Sym2.map (ψ v))))→
      ∀β:ℝ,0<β→β≤1→δ≤(β/100)^2→100/β≤(n:ℝ)→2/Real.sqrt δ≤(n:ℝ)→Fintype.card U≤n→
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>σ (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/((m:ℝ)+1)+4*(n:ℝ)^(3/4:ℝ))→
      (∀v,(Jbad.degree v:ℝ)≤δ*n)→
      (∀u,IsExtendingList Dfree
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
      (∀u,Disjoint (E u\(M u).image prescribedArcPhysical) Jbad.edgeFinset) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*n) ∧
      (∀u x,x∈(a u).oldDomain→f u x=ψ u x) ∧
      (∀u (x:{x // x∈(a u).remaining}),f u x.1=Φ u x) ∧
      (∀u,(((F u).induce (S u)).edgeFinset).image (Sym2.map (f u))=
        (a u).deletedEdges.image (Sym2.map (ψ u)) ∪
          (((a u).graph.induce (fun x=>x∈(a u).remaining)).edgeFinset).image (Sym2.map (Φ u))) ∧
      (∀u x y,((F u).induce (S u)).Adj x y→P.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) ((F u).induce (S u)) (f u))
        (partialFactorPhysicalEdgesPoly (X v) ((F v).induce (S v)) (f v)))   :=by
  obtain ⟨m₀,N₀,hm₀,hPlace⟩:=ordinary_assignment_unreserved_sampled_load_placement δ hδ
  refine ⟨m₀,hm₀,?_⟩
  intro m hm d hd θ hθ err herr
  have hm7:7≤m:=by omega
  obtain ⟨N₁,hBounds⟩:=ordinary_unreserved_family_size_and_capacity_from_matching_eventually m d hm7 hd θ hθ err herr
  refine ⟨max N₀ N₁,?_⟩
  intro n K hnN U _ _ hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hrsclass hclass π hnoshort σ raw t Jret ζ matchErr κ hgood Cres hsize hres hcounts Rim
    H RM state RR φ L W hW Q Row A B S J X a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch hQ hζ he hrate hrow hbudget errUpper herrUpper0 herrUpper hmatchUpper αCap b hα hb hbudgetCap P Target G Jbad hG hedit hEvent hbsmall hbδ Dstar Dfree hDstar hDD ext inner hempty hsupp hinner Old hOldEq ψ hmarker hψ hOld Host Del hHP hstar hselected hdir hOO β hβ hβ1 hδbound hnβ hn' hU hOcc hJ hext
  have hdegree:∀v,(G.degree v:ℝ)≤b*n:=by
    intro v
    rw [hG]
    have hh:=added_graph_degree_le_symmetric_edit Target (longPhysicalStateGraph P σ {0,1,2,3,4}) (b*n) hedit v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hOG:∀u,Disjoint ((a u).deletedEdges.image (Sym2.map (ψ u))) G.edgeFinset:=by
    intro u
    rw [hG]
    have hh:=ordinary_old_family_avoids_sample_added_edges P Host Del Target hHP π d σ
      (fun u=>(F u).induce (S u)) a hempty hs₁ ψ hdir u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hbds:=hBounds (by omega) hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hrsclass hclass π hnoshort raw t Jret ζ matchErr κ hgood Cres hsize hres hcounts Rim L W hW a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch hQ hζ he hrate hrow δ hbudget errUpper herrUpper0 herrUpper hmatchUpper αCap b hα hb hbudgetCap G hdegree
  have hsize':∀u,(Fintype.card {x // x∈(a u).remaining}:ℝ)≤δ*n:=fun u=>(hbds u).1
  have hcap':∀u,8*(residualSubtypeSet (a u).remaining (a u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*n)⌉₊+10≤Fintype.card {x // x∈(a u).remaining}:=fun u=>(hbds u).2
  have hinst:ordinaryMatchingEditComplementFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  have hPlace':=hPlace m hm (n:=n) (by omega) (U:=U) (J:=J)
  rw [←hinst] at hPlace'
  obtain ⟨D,pieces,M,Bout,g,Φ,hgraph,harcs,hM,hOldM,hMlist,hMsub,hinj,hB,hΦg,hΦL,hΦarc,hEpair,hME,hcover,havoid,hdeg⟩:=
    hPlace' π d σ αCap hEvent t Jret G Jbad Dstar Dfree hDstar hDD F hF Cres a ext inner hc hd' hs₁ hsupp hinner hEmbed Old hOldEq ψ hmarker hψ hOld b hb hbsmall hbδ hdegree hcap' β hβ hβ1 hδbound hnβ hn' hU hsize' hOcc hJ hext
  letI:Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hreg:∀u,((F u).induce (S u)).IsRegularOfDegree 2:=fun u=>(ordinary_unreserved_factor_paths (F u) (hF u) (Cres u)).1
  have hCycle:∀u,(a u).t.biUnion (fun j=>((a u).C j).support.toFinset)⊆(a u).Cembed:=by
    intro u
    rw [hEmbed u]
  obtain ⟨f,hfold,hfnew⟩:=empty_final_dependent_residual_glue hempty (fun u (_:A u)=>(m+1)*d) inner
    (fun u=>(F u).induce (S u)) hreg a hCycle Old hOldEq ψ hψ Bout g Φ
    (fun u=>rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (fun u=>prescribedMatchingEndpoints (M u)) (fun u=>(hB u).1) hinj
    (fun u=>(hB u).2.1) hΦg (fun u=>(hB u).2.2.1) hOldM hΦL (fun u=>(hOld u).symm)
  have hpartition:∀u,(((F u).induce (S u)).edgeFinset).image (Sym2.map (f u))=
      (a u).deletedEdges.image (Sym2.map (ψ u)) ∪
        (((a u).graph.induce (fun x=>x∈(a u).remaining)).edgeFinset).image (Sym2.map (Φ u)):=by
    intro u
    have hh:=(a u).glued_factor_edge_images (hreg u) (hCycle u) (ψ u) (f u) (Φ u) (hfold u) (hfnew u)
    convert hh using 1 <;> congr 2 <;> apply graph_edge_finset_instance_eq
  have hgraphEdges:∀u,(prescribedDependentGraph pieces u).edgeFinset=
      ((a u).graph.induce (fun x=>x∈(a u).remaining)).edgeFinset:=by
    intro u
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [hgraph u]
    rfl
  have hpart:∀u,(((F u).induce (S u)).edgeFinset).image (Sym2.map (f u))=
      (a u).deletedEdges.image (Sym2.map (ψ u)) ∪
      ((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u)):=by
    intro u
    rw [hgraphEdges u]
    exact hpartition u
  obtain ⟨hhost,hdisjoint⟩:=ordinary_empty_final_physical_completion P Host Del hHP π d σ
    (fun u=>(F u).induce (S u)) a hempty hs₁ ψ (fun u=>(f u : X u→Fin n)) pieces Bout g Φ M G Dstar Dfree hstar hselected hdir
    hΦg (fun u=>(hB u).2.2.2) hΦarc hMsub hpart hOO hOG hEpair
  exact ⟨D,pieces,M,Bout,g,Φ,f,hgraph,harcs,hM,hOldM,hMlist,hMsub,hinj,hB,hΦg,hΦL,hΦarc,hEpair,hME,hcover,havoid,hdeg,hfold,hfnew,hpartition,hhost,hdisjoint⟩
end Oberwolfach
