module

public import Oberwolfach.ActualResidualReservedMatchingLists
public import Oberwolfach.ActualReservedMatchingFromOuterLists
public import Oberwolfach.ActualReservedSpokeInnerExclusions
public import Oberwolfach.ResidualActualFamilyForPositions
public import Oberwolfach.ResidualActualWithAssignedBadEdges
public import Oberwolfach.ResidualActualCompletedPieceFamily

@[expose] public section
/-! Assign the actual bad edges, embed the actual residual source graphs,
protect the old physical packing, and glue the source embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq K] [DecidableEq J]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_factor_remainder_with_outer_reserved_lists
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2):
    ∃ (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i)) ∧
      (∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset) ∧
      (∀i x y,D i x y ↔ (x,y)∈sourcePieceArcsUnion (orig i)) ∧
      ∀ a:∀i,ActualResidualData (K:=K) (J:=J) (F i),
      ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}),
      (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i))) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x.1 y.1 ∧ (a i).graph.Adj x.1 y.1) ∧
      ∀ (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
        (ψ:∀i,X i→V) (hψ:∀i,Set.InjOn (ψ i) (↑(a i).oldDomain:Set (X i)))
        (Kbad Jbad:SimpleGraph V) (Sbase:Sym2 V→Finset I) (Bad:V→Finset I) (inner:Finset I) (Z:I→Finset V)
        (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (Outer:I→Finset V)
        (hHoldOuter:∀v i,Hold false v i→v∈Outer i)
        (hOldOuter:∀i,Disjoint ((a i).oldDomain.image (ψ i)) (Outer i))
        (hPairOuter:∀e∈Kbad.edgeFinset,∀i∈Sbase e,∀v∈e.toFinset,v∈Outer i)
        (hOutside:∀e∈Kbad.edgeFinset,Disjoint (Sbase e) inner)
        (hOldZ:∀i,Disjoint ((a i).oldDomain.image (ψ i)) (Z i)) (houter:∀i,i∉inner→Z i=∅)
        (α b:ℝ) (hα:0<α) (hb:0≤b) (hbsmall:b≤α/16) (hnV:0<Fintype.card V)
        (hLbase:∀e∈Kbad.edgeFinset,2*α*Fintype.card V≤((Sbase e).card:ℝ))
        (hReserveSize:2*(C.card:ℝ)≤α*Fintype.card V)
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
        (hListOld:∀i,Disjoint (Lists i) ((a i).oldDomain.image (ψ i))),
      let Reserved:=actualReservedOrdinarySpokeLabels C Hold
      let Lbad:=reservedSpokeMatchingList Sbase Reserved;
      ∃ (assign:Sym2 V→I) (orient:Sym2 V→V×V)
        (B:∀i,Finset {x // x∈(a i).remaining})
        (g Φ:∀i,{x // x∈(a i).remaining}→V) (f:∀i,X i→V),
        (∀i,Function.Injective (f i) ∧ (∀x∈(a i).oldDomain,f i x=ψ i x) ∧
          (∀x:{x // x∈(a i).remaining},f i x.1=Φ i x)) ∧
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
        (∀v,(((Finset.univ.filter (fun z:(Σi,{x // x∈(a i).remaining})=>z.2∉B z.1)).filter
          (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
        (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
        (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) ∧
        ((PairwisePhysicalDisjoint (fun i=>((a i).deletedEdges).image (Sym2.map (ψ i))))→
          (∀i,((a i).deletedEdges).image (Sym2.map (ψ i))⊆Pack)→
          PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (f i))) ∧
          Kbad.edgeFinset⊆Finset.univ.biUnion (fun i=>((F i).edgeFinset).image (Sym2.map (f i)))) ∧
        ((∀i,((a i).deletedEdges).image (Sym2.map (ψ i))⊆Pack)→
          Disjoint Pack Jbad.edgeFinset→
          ∀i,Disjoint (((F i).edgeFinset).image (Sym2.map (f i))) Jbad.edgeFinset) ∧
        (∀ (Y Block:I→Finset V) (Inner:Finset V),
          (∀i,Z i⊆Inner\((Outer i∪Y i)∩Inner))→
          (∀i,Disjoint (Lists i) (Reserved i))→
          ∀ Hnew:Bool→V→I→Prop,
          (∀v i,Hnew true v i↔v∈Y i)→
          (∀v i,Hnew false v i↔v∉(Finset.univ.image (f i))∧v∉Block i∧v∉Y i)→
          (∀v i,Sum.inr (v,i)∈C→Hold true v i→v∈Y i)→
          (∀v i,Hold false v i→v∉Y i)→
          (∀v i,Sum.inr (v,i)∈C→Hold false v i→v∉Block i)→
          (∀i,Disjoint (Finset.univ.image (f i)) (Reserved i)) ∧
          ∀b v i,Sum.inr (v,i)∈C→Hold b v i→Hnew b v i) :=by
  obtain ⟨D,orig,hpair0,hcycles,hwhole,hD,hres⟩:=actual_factor_remainder_assigned_and_glued (K:=K) (J:=J) (V:=V) F hF
  refine ⟨D,orig,hpair0,hcycles,hwhole,hD,?_⟩
  intro a
  obtain ⟨pieces,hgraph,harcs,hcont⟩:=hres a
  refine ⟨pieces,hgraph,harcs,?_⟩
  intro hCycle ψ hψ Kbad Jbad Sbase Bad inner Z C Hold Outer hHoldOuter hOldOuter hPairOuter hOutside hOldZ houter α b hα hb hbsmall hnV hLbase hReserveSize hBad hKbad hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext hListOld Reserved Lbad
  have hLists:=actual_reserved_matching_inputs_from_outer_lists C Hold Sbase Kbad inner
    (fun i=>(a i).oldDomain.image (ψ i)) Outer Bad α hLbase hReserveSize hOutside hPairOuter hOldOuter
  have hLbad:=hLists.1
  have hOutside':=hLists.2.1
  have hOldShield':=hLists.2.2.1
  obtain ⟨assign,orient,B,g,Φ,f,hf,hBg,hEnd,hEndList,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree⟩:=
    hcont hCycle ψ hψ Kbad Jbad Lbad Bad inner Z hOutside' hOldZ houter hOldShield' α b hα hb hbsmall hnV hLbad hBad hKbad hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext hListOld
  have hOldAgree:∀i x,x∈(a i).oldDomain→f i x=ψ i x:=fun i=>(hf i).2.1
  have hRemAgree:∀i (x:{x // x∈(a i).remaining}),f i x.1=Φ i x:=fun i=>(hf i).2.2
  refine ⟨assign,orient,B,g,Φ,f,hf,hBg,hEnd,hEndList,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree,?_,?_,?_⟩
  · intro hOld hOldPack
    exact actual_piece_family_glued_physical_edges F hF a pieces hgraph hCycle ψ f Φ hOldAgree hRemAgree Pack Kbad.edgeFinset hOld hOldPack hPair hPack hKcover
  · intro hOldPack hPackRes
    exact actual_glued_factor_avoids_reserved_edges F hF a pieces hgraph hCycle ψ f Φ hOldAgree hRemAgree Pack Jbad.edgeFinset hOldPack hPackRes hJavoid
  · intro Y Block Inner hRequiredInner hListAvoid Hnew hMarked hOrdinary hFixed hDisjoint hBlock
    have hsets:=actual_reserved_spokes_in_outer_and_inner_exclusion C Hold Outer Y Inner hHoldOuter
    have hlabel:∀v i,Sum.inr (v,i)∈C→Hold false v i→v∈Reserved i:=by
      intro v i hc hh
      exact (actual_reserved_ordinary_spoke_labels_mem C Hold i v).mpr ⟨hc,hh⟩
    exact actual_residual_reserved_spokes_from_matching_lists F hF a hCycle ψ f hψ Φ g B Lists Reserved
      hOldAgree hRemAgree hΦold hL (fun i=>prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient i))
      Z Kbad Lbad (fun i=>(hBg i).2.2) hEndList hLists.2.2.2 Outer (fun i=>(Outer i∪Y i)∩Inner)
      Inner hOldOuter hsets.1 hRequiredInner hsets.2 hListAvoid C Hold Hnew Y Block
      hMarked hOrdinary hFixed hDisjoint hlabel hBlock
end Oberwolfach
