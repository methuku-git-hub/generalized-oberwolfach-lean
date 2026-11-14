module

public import Oberwolfach.ActualFixedSourceResidualReady
public import Oberwolfach.CompleteRemainderWithDisjointTargetsTracked
public import Oberwolfach.ResidualActualLateIndicesForPositions
public import Oberwolfach.ActualPrescribedAvoidsDeletedInteriors
public import Oberwolfach.ActualComplementEmbeddingGlue
public import Oberwolfach.ActualRestrictedEdgePackingDependent
public import Oberwolfach.ResidualActualFamilyForPositions
public import Oberwolfach.CompleteRemainderAndGlue

@[expose] public section
/-! Assign the actual bad edges, embed the actual residual source graphs,
protect the old physical packing, and glue the source embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_fixed_source_late_indices_complement_disjoint_targets_tracked
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i)))
    (hpair0:∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hcycles:∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i))
    (hwhole:∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset)
    (hD:∀i x y,D i x y↔(x,y)∈sourcePieceArcsUnion (orig i)):
      ∀ (K J:I→Type) [∀i,DecidableEq (K i)] [∀i,DecidableEq (J i)],
      ∀ a:∀i,ActualResidualData (K:=K i) (J:=J i) (F i),
      ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}),
      (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i))) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x.1 y.1 ∧ (a i).graph.Adj x.1 y.1) ∧
      ∀ (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
        (Interiors:∀i,Finset (X i)) (hDR:∀i,Disjoint (Interiors i) (a i).remaining)
        (ψ:∀i,X i→V) (hψ:∀i,Set.InjOn (ψ i) (↑((a i).oldDomain\Interiors i):Set (X i)))
        (Kbad Jbad:SimpleGraph V) (Lbad:Sym2 V→Finset I) (Bad:V→Finset I) (inner:Finset I) (Z:I→Finset V)
        (hOutside:∀e∈Kbad.edgeFinset,Disjoint (Lbad e) inner)
        (hOldZ:∀i,Disjoint (((a i).oldDomain\Interiors i).image (ψ i)) (Z i))
        (hZavoid:∀i e v,e∈Kbad.edgeFinset→v∈e.toFinset→i∈Lbad e→v∉Z i)
        (hOldShield:∀i e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈((a i).oldDomain\Interiors i).image (ψ i)→i∈Lbad e→i∈Bad v)
        (α b:ℝ) (hα:0<α) (hb:0≤b) (hbsmall:b≤α/16) (hnV:0<Fintype.card V)
        (hLbad:∀e∈Kbad.edgeFinset,α*Fintype.card V≤((Lbad e).card:ℝ))
        (hBad:∀v,((Bad v).card:ℝ)≤b*Fintype.card V)
        (hKbad:∀v,(Kbad.degree v:ℝ)≤b*Fintype.card V)
        (hcapacity:∀i,8*(residualSubtypeSet (a i).remaining (a i).prescribed).card+
          8*⌈4*(Kbad.edgeFinset.card:ℝ)/(α*Fintype.card V)⌉₊+4*(Z i).card+10≤Fintype.card {x // x∈(a i).remaining})
        (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
        (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
        (hI:(Fintype.card I:ℝ)≤Fintype.card V)
        (hsize:∀i,(Fintype.card {x // x∈(a i).remaining}:ℝ)≤δ*Fintype.card V)
        (hold:∀v,((Finset.univ.filter (fun i=>v∈
          (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1))).card:ℝ)+Kbad.degree v+
          ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ)≤δ*Fintype.card V)
        (hJ:∀v,(Jbad.degree v:ℝ)≤δ*Fintype.card V) (hKJ:Disjoint Kbad.edgeFinset Jbad.edgeFinset)
        (Dfree Dstar:V→V→Prop) (hDD:∀x y,Dfree x y→Dstar x y)
        (hDstar:∀x y,Kbad.Adj x y→Dstar x y ∨ Dstar y x)
        (Pack:Finset (Sym2 V)) (hKPack:Disjoint Kbad.edgeFinset Pack) (hDPack:∀x y,Dfree x y→s(x,y)∉Pack)
        (Lists:I→Finset V) (hext:∀i,IsExtendingList Dfree (Lists i) β)
        (hListOld:∀i,Disjoint (Lists i) (((a i).oldDomain\Interiors i).image (ψ i)))
        (FinalEdges:∀i,Finset (Sym2 (X i)))
        (hOldPair:∀i j,i≠j→Disjoint (((a i).deletedEdges\FinalEdges i).image (Sym2.map (ψ i)))
          (((a j).deletedEdges\FinalEdges j).image (Sym2.map (ψ j))))
        (hOldPack:∀i,((a i).deletedEdges\FinalEdges i).image (Sym2.map (ψ i))⊆Pack),
      ∃ (assign:Sym2 V→I) (orient:Sym2 V→V×V)
        (B:∀i,Finset {x // x∈(a i).remaining})
        (g Φ:∀i,{x // x∈(a i).remaining}→V) (fC:∀i,{x // x∉Interiors i}↪V),
        (∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e) ∧
        (∀i,(prescribedAssignedArcs Kbad assign orient i).card≤⌈4*(Kbad.edgeFinset.card:ℝ)/(α*Fintype.card V)⌉₊) ∧
        (∀i (x:{x // x∉Interiors i}),x.val∈(a i).oldDomain→fC i x=ψ i x.val) ∧
        (∀i (x:{x // x∈(a i).remaining}) (hx:x.val∉Interiors i),fC i ⟨x.val,hx⟩=Φ i x) ∧
        (∀i,residualSubtypeSet (a i).remaining (a i).prescribed⊆B i ∧
          (∀x∈residualSubtypeSet (a i).remaining (a i).prescribed,g i x=ψ i x.1) ∧
          (B i).image (g i)=
            (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)∪
              prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)∪Z i) ∧
        (∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)→i∉Bad v) ∧
        (∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)→
          ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ i∈Lbad e) ∧
        (∀i x,x∈B i→Φ i x=g i x) ∧
        (∀i v,v∈Z i→∃x,Φ i x=v) ∧
        (∀i x,x∉B i→Φ i x∈Lists i) ∧
        (∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
          ((x∉B i ∨ y∉B i)→Dfree (Φ i x) (Φ i y))) ∧
        let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
        PairwisePhysicalDisjoint E ∧ Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
        (∀i,Disjoint (E i) Jbad.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
        (∀i j,i≠j→Disjoint
          (((((F i).deleteEdges (↑(FinalEdges i):Set (Sym2 (X i)))).induce {x | x∉Interiors i}).edgeFinset).image (Sym2.map (fC i)))
          (((((F j).deleteEdges (↑(FinalEdges j):Set (Sym2 (X j)))).induce {x | x∉Interiors j}).edgeFinset).image (Sym2.map (fC j)))) ∧
        (∀v,(((Finset.univ.filter (fun z:(Σi,{x // x∈(a i).remaining})=>z.2∉B z.1)).filter
          (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
        (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
        (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) :=by
  have hres:=actual_fixed_source_residuals_ready_for_positions F hF D orig hpair0 hcycles hwhole hD
  intro K J _ _ a
  obtain ⟨pieces,hapart,hvalid,hcover,hgraph,harcs,hA,harc,hoverlap,hdom⟩:=hres K J a
  refine ⟨pieces,hgraph,harcs,?_⟩
  intro hCycle Interiors hDR ψ hψ Kbad Jbad Lbad Bad inner Z hOutside hOldZ hZavoid hOldShield α b hα hb hbsmall hnV hLbad hBad hKbad hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext hListOld FinalEdges hOldPair hOldPack
  letI:Nonempty V:=Fintype.card_pos_iff.mp hnV
  let Old:=fun i=>(a i).oldDomain\Interiors i
  have hPresOld:∀i,(a i).prescribed⊆Old i:=fun i=>
    actual_prescribed_subset_old_without_disjoint_interiors (a i) (hF i) (Interiors i) (hDR i)
  let A:=fun i=>residualSubtypeSet (a i).remaining (a i).prescribed
  let f₀:=fun i (x:{x // x∈(a i).remaining})=>ψ i x.1
  have hAinj:∀i,Set.InjOn (f₀ i) (↑(A i):Set {x // x∈(a i).remaining}):=by
    intro i x hx y hy hxy
    apply Subtype.ext
    apply hψ i (hPresOld i ?_) (hPresOld i ?_) hxy
    · simpa [A,residualSubtypeSet] using hx
    · simpa [A,residualSubtypeSet] using hy
  have hAold:∀i,(A i).image (f₀ i)⊆(Old i).image (ψ i):=by
    intro i v hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨x.1,hPresOld i (by simpa [A,residualSubtypeSet] using hx),rfl⟩
  obtain ⟨assign,orient,B,g,Φ,hOrient,hMcap,hBg,hEnd,hEndList,hΦinj,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree⟩:=
    complete_remainder_with_image_and_disjoint_targets_tracked pieces (by intro i p hp;exact (hvalid i p hp).1) hapart A hA f₀ hAinj
      Kbad Jbad Lbad Bad inner Z (fun i=>(Old i).image (ψ i)) hAold hOldShield hOutside hOldZ hZavoid
      α b hα hb hbsmall hnV hLbad hBad hKbad harc hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ
      Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext
  have hOldC:∀i,Disjoint ((Old i).image (ψ i)) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)):=by
    intro i
    apply Finset.disjoint_left.mpr
    intro v hvOld hvC
    obtain ⟨e,he,hve,hi⟩:=hEndList i v hvC
    exact hEnd i v hvC (hOldShield i e v he hve hvOld hi)
  have hΦinj':∀i,Function.Injective (Φ i):=by
    intro i x y hxy
    exact hΦinj i (by simp) (by simp) hxy
  have hglue:∀i,∃fC:{x // x∉Interiors i}↪V,
      (∀x:{x // x∉Interiors i},x.val∈(a i).oldDomain→fC x=ψ i x.val) ∧
      (∀x:{x // x∈(a i).remaining},∀hx:x.val∉Interiors i,fC ⟨x.val,hx⟩=Φ i x):=by
    intro i
    exact actual_residual_embeddings_glue_on_complement (a i) (hF i) (hCycle i) (Interiors i) (hDR i)
      (ψ i) (hψ i) (B i) (g i) (Φ i) (Lists i) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i)) (Z i)
      (hBg i).1 (hΦinj' i) (hBg i).2.1 (hΦold i) (hBg i).2.2
      (hOldC i) (hOldZ i) (hL i) (hListOld i)
  choose fC hC hR using hglue
  have hNewPair:∀i j,i≠j→Disjoint
      ((((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i)))
      ((((a j).graph.induce (↑(a j).remaining:Set (X j))).edgeFinset).image (Sym2.map (Φ j))):=by
    intro i j hij
    have hi:((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))=
        (((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i)):=by
      rw [hgraph i]
      congr 1
      apply Finset.coe_injective
      simp only [SimpleGraph.coe_edgeFinset]
      rfl
    have hj:((prescribedDependentGraph pieces j).edgeFinset).image (Sym2.map (Φ j))=
        (((a j).graph.induce (↑(a j).remaining:Set (X j))).edgeFinset).image (Sym2.map (Φ j)):=by
      rw [hgraph j]
      congr 1
      apply Finset.coe_injective
      simp only [SimpleGraph.coe_edgeFinset]
      rfl
    rw [←hi,←hj]
    exact hPair i j hij
  have hNewPack:∀i,Disjoint
      ((((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i))) Pack:=by
    intro i
    have hi:((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))=
        (((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i)):=by
      rw [hgraph i]
      congr 1
      apply Finset.coe_injective
      simp only [SimpleGraph.coe_edgeFinset]
      rfl
    rw [←hi]
    exact hPack i
  have hPacked:=actual_restricted_edge_images_packed_dependent F hF a hCycle Interiors FinalEdges fC ψ Φ hC
    (by intro i x hx;exact hR i ⟨x.val,hx⟩ x.property) Pack hOldPair hOldPack hNewPair hNewPack
  exact ⟨assign,orient,B,g,Φ,fC,hOrient,hMcap,hC,hR,hBg,hEnd,hEndList,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hPacked,hFree,hUnion,hDegree⟩
end Oberwolfach
