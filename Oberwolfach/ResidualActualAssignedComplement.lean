module

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
variable {I K J V:Type} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq K] [DecidableEq J]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_factor_remainder_assigned_and_complement_glued
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
      ∀ (Final:∀i,Finset (X i)) (hFinal:∀i,Disjoint (Final i) (a i).remaining)
        (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
        (ψ:∀i,X i→V) (hψ:∀i,Set.InjOn (ψ i) (↑((a i).oldDomain\Final i):Set (X i)))
        (Kbad Jbad:SimpleGraph V) (Lbad:Sym2 V→Finset I) (Bad:V→Finset I) (inner:Finset I) (Z:I→Finset V)
        (hOutside:∀e∈Kbad.edgeFinset,Disjoint (Lbad e) inner)
        (hOldZ:∀i,Disjoint (((a i).oldDomain\Final i).image (ψ i)) (Z i)) (houter:∀i,i∉inner→Z i=∅)
        (hOldShield:∀i e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈((a i).oldDomain\Final i).image (ψ i)→i∈Lbad e→i∈Bad v)
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
        (hListOld:∀i,Disjoint (Lists i) (((a i).oldDomain\Final i).image (ψ i))),
      ∃ (assign:Sym2 V→I) (orient:Sym2 V→V×V)
        (B:∀i,Finset {x // x∈(a i).remaining})
        (g Φ:∀i,{x // x∈(a i).remaining}→V) (fC:∀i,{x // x∉Final i}↪V),
        (∀i (x:{x // x∉Final i}),x.val∈(a i).oldDomain→fC i x=ψ i x.val) ∧
        (∀i (x:{x // x∈(a i).remaining}) (hx:x.val∉Final i),fC i ⟨x.val,hx⟩=Φ i x) ∧
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
        (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) :=by
  obtain ⟨D,orig,hpair0,hcycles,hwhole,hD,hres⟩:=actual_factor_residuals_ready_for_positions (K:=K) (J:=J) F hF
  refine ⟨D,orig,hpair0,hcycles,hwhole,hD,?_⟩
  intro a
  obtain ⟨pieces,hapart,hvalid,hcover,hgraph,harcs,hA,harc,hoverlap,hdom⟩:=hres a
  refine ⟨pieces,hgraph,harcs,?_⟩
  intro Final hFinal hCycle ψ hψ Kbad Jbad Lbad Bad inner Z hOutside hOldZ houter hOldShield α b hα hb hbsmall hnV hLbad hBad hKbad hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext hListOld
  letI:Nonempty V:=Fintype.card_pos_iff.mp hnV
  let A:=fun i=>residualSubtypeSet (a i).remaining (a i).prescribed
  let Old:=fun i=>(a i).oldDomain\Final i
  let f₀:=fun i (x:{x // x∈(a i).remaining})=>ψ i x.1
  let embed:=fun i=> (⟨Subtype.val,Subtype.val_injective⟩ : {x // x∈(a i).remaining}↪X i)
  have hdom':∀i (x:{x // x∈(a i).remaining}),x∈A i ↔ embed i x∈Old i:=by
    intro i x
    rw [hdom i x]
    change x.val∈(a i).oldDomain ↔ x.val∈(a i).oldDomain\Final i
    simp only [Finset.mem_sdiff]
    constructor
    · intro hx
      refine ⟨hx,?_⟩
      intro hfinal
      exact Finset.disjoint_left.mp (hFinal i) hfinal x.property
    · exact And.left
  have hAinj:∀i,Set.InjOn (f₀ i) (↑(A i):Set {x // x∈(a i).remaining}):=by
    intro i x hx y hy hxy
    apply Subtype.ext
    exact hψ i ((hdom' i x).1 hx) ((hdom' i y).1 hy) hxy
  obtain ⟨assign,orient,B,g,Φ,f,hinj,holdf,hresf,hBg,hEnd,hEndList,hΦinj,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree⟩:=
    complete_remainder_and_glue_from_lists pieces (by intro i p hp;exact (hvalid i p hp).1) hapart A hA f₀ hAinj
      embed Old ψ hdom' hψ (by intro i x hx;rfl)
      Kbad Jbad Lbad Bad inner Z hOutside hOldZ houter hOldShield α b hα hb hbsmall hnV hLbad hBad hKbad
      harc hcapacity β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hKJ Dfree Dstar hDD hDstar Pack hKPack hDPack Lists hext hListOld
  have hmem:∀i (x:{x // x∉Final i}),x.val∈Old i∪Finset.univ.image (embed i):=by
    intro i x
    have hx:x.val∈(a i).oldDomain ∨ x.val∈(a i).remaining:=by
      have hh:x.val∈(a i).oldDomain∪(a i).remaining:=by
        rw [(a i).old_domain_union_remaining (hCycle i)]
        exact Finset.mem_univ _
      exact Finset.mem_union.mp hh
    rcases hx with ho | hr
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ho,x.property⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⟨x.val,hr⟩,Finset.mem_univ _,rfl⟩
  let fC:∀i,{x // x∉Final i}↪V:=fun i=>⟨fun x=>f i x.val,by
    intro x y hxy
    apply Subtype.ext
    exact hinj i (hmem i x) (hmem i y) hxy⟩
  refine ⟨assign,orient,B,g,Φ,fC,?_,?_,hBg,hEnd,hEndList,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPack,hFree,hUnion,hDegree⟩
  · intro i x hx
    exact holdf i x.val (Finset.mem_sdiff.mpr ⟨hx,x.property⟩)
  · intro i x hx
    exact hresf i x
end Oberwolfach
