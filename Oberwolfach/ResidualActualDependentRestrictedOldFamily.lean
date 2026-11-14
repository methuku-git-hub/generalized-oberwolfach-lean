module

public import Oberwolfach.ResidualActualDependentFamilyForPositions
public import Oberwolfach.ResidualActualFamilyForPositions
public import Oberwolfach.ResidualActualEmbeddingGlue
public import Oberwolfach.PrescribedAllVerticesEmbedding

@[expose] public section
/-! Apply the prescribed-position and embedding theorem to the actual
residual source graphs, then glue back the previously embedded source
vertices. All matching, list, multiplicity, and avoidance hypotheses below
are the hypotheses of that theorem for the actual residual domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] {K J:I→Type} [∀i,DecidableEq (K i)] [∀i,DecidableEq (J i)]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_factor_residuals_dependent_embed_with_restricted_old_domain
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2):
    ∃ (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i)) ∧
      (∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset) ∧
      (∀i x y,D i x y ↔ (x,y)∈sourcePieceArcsUnion (orig i)) ∧
      ∀ a:∀i,ActualResidualData (K:=K i) (J:=J i) (F i),
      ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}),
      (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i))) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x.1 y.1 ∧ (a i).graph.Adj x.1 y.1) ∧
      ∀ (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
        (Old:∀i,Finset (X i)) (hPresOld:∀i,(a i).prescribed⊆Old i)
        (ψ:∀i,X i→V) (hψ:∀i,Set.InjOn (ψ i) (↑(Old i):Set (X i)))
        (M:I→Finset (V×V)) (hM:∀i,IsPrescribedOrientedMatching (M i)) (Z:I→Finset V)
        (hOldM:∀i,Disjoint ((Old i).image (ψ i)) (prescribedMatchingEndpoints (M i)))
        (hOldZ:∀i,Disjoint ((Old i).image (ψ i)) (Z i))
        (hMZ:∀i,Disjoint (prescribedMatchingEndpoints (M i)) (Z i))
        (hcapacity:∀i,8*(residualSubtypeSet (a i).remaining (a i).prescribed).card+
          8*(M i).card+4*(Z i).card+10≤Fintype.card {x // x∈(a i).remaining})
        (Jbad:SimpleGraph V) (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
        (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
        (hI:(Fintype.card I:ℝ)≤Fintype.card V)
        (hsize:∀i,(Fintype.card {x // x∈(a i).remaining}:ℝ)≤δ*Fintype.card V)
        (hold:∀v,((Finset.univ.filter (fun i=>v∈
          (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)∪
          prescribedMatchingEndpoints (M i)∪Z i)).card:ℝ)≤δ*Fintype.card V)
        (hJ:∀v,(Jbad.degree v:ℝ)≤δ*Fintype.card V)
        (hpair:PairwisePhysicalDisjoint (fun i=>(M i).image prescribedArcPhysical))
        (Dfree Dstar:V→V→Prop) (hDD:∀x y,Dfree x y→Dstar x y)
        (hMstar:∀i x y,(x,y)∈M i→Dstar x y)
        (L:I→Finset V) (hext:∀i,IsExtendingList Dfree (L i) β)
        (hL:∀i,Disjoint (L i) ((Old i).image (ψ i))),
      ∃ (B:∀i,Finset {x // x∈(a i).remaining})
        (g Φ:∀i,{x // x∈(a i).remaining}→V),
        (∀i,Function.Injective (Φ i)) ∧
        (∀i,residualSubtypeSet (a i).remaining (a i).prescribed⊆B i ∧
          (∀x∈residualSubtypeSet (a i).remaining (a i).prescribed,g i x=ψ i x.1) ∧
          (B i).image (g i)=
            (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)∪
              prescribedMatchingEndpoints (M i)∪Z i ∧
          (prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image (Prod.map (g i) (g i))=M i) ∧
        (∀i x,x∈B i→Φ i x=g i x) ∧
        (∀i v,v∈Z i→∃x,Φ i x=v) ∧
        (∀i x,x∉B i→Φ i x∈L i) ∧
        (∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
          ((x∉B i ∨ y∉B i)→Dfree (Φ i x) (Φ i y))) ∧
        let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
        PairwisePhysicalDisjoint E ∧ (∀i,(M i).image prescribedArcPhysical⊆E i) ∧
        (∀i,Disjoint (E i\(M i).image prescribedArcPhysical) Jbad.edgeFinset) ∧
        (∀v,(((prescribedDependentFreeVertices (prescribedPadSingletons pieces) B).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
        (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
        (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) :=by
  obtain ⟨D,orig,hpair0,hcycles,hwhole,hD,hres⟩:=actual_factor_residuals_dependent_ready_for_positions (K:=K) (J:=J) F hF
  refine ⟨D,orig,hpair0,hcycles,hwhole,hD,?_⟩
  intro a
  obtain ⟨pieces,hapart,hvalid,hcover,hgraph,harcs,hA,harc,hoverlap,hdom⟩:=hres a
  refine ⟨pieces,hgraph,harcs,?_⟩
  intro hCycle Old hPresOld ψ hψ M hM Z hOldM hOldZ hMZ hcapacity Jbad β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hpair Dfree Dstar hDD hMstar L hext hL
  let A:=fun i=>residualSubtypeSet (a i).remaining (a i).prescribed
  let f₀:=fun i (x:{x // x∈(a i).remaining})=>ψ i x.1
  have hAinj:∀i,Set.InjOn (f₀ i) (↑(A i):Set {x // x∈(a i).remaining}):=by
    intro i x hx y hy hxy
    apply Subtype.ext
    apply hψ i (hPresOld i ?_) (hPresOld i ?_) hxy
    · simpa [A,residualSubtypeSet] using hx
    · simpa [A,residualSubtypeSet] using hy
  have hsub:∀i,(A i).image (f₀ i)⊆(Old i).image (ψ i):=by
    intro i v hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨x.1,hPresOld i (by simpa [A,residualSubtypeSet] using hx),rfl⟩
  have hOldM':∀i,Disjoint ((A i).image (f₀ i)) (prescribedMatchingEndpoints (M i)):=fun i=>(hOldM i).mono_left (hsub i)
  have hOldZ':∀i,Disjoint ((A i).image (f₀ i)) (Z i):=fun i=>(hOldZ i).mono_left (hsub i)
  obtain ⟨B,g,Φ,hBg,hΦinj,hΦold,hZ,hΦL,hΦarc,hΦpair,hMcover,hJavoid,hLoad,hUnion,hDegree⟩:=
    prescribed_positions_and_family_embedding_all_vertices pieces (by intro i p hp;exact (hvalid i p hp).1) hapart
      A hA f₀ hAinj M hM Z hOldM' hOldZ' hMZ harc hcapacity Jbad β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold hJ hpair Dfree Dstar hDD hMstar L hext
  have hΦinj':∀i,Function.Injective (Φ i):=by
    intro i x y hxy
    exact hΦinj i (by simp) (by simp) hxy
  refine ⟨B,g,Φ,hΦinj',?_,hΦold,?_,?_,hΦarc,hΦpair,hMcover,hJavoid,hLoad,hUnion,hDegree⟩
  · intro i
    exact ⟨(hBg i).1,(hBg i).2.2.1,(hBg i).2.2.2.1,(hBg i).2.2.2.2.1⟩
  · intro i v hv
    obtain ⟨x,_,hx⟩:=hZ i v hv
    exact ⟨x,hx⟩
  · intro i x hx
    exact hΦL i x (by simp) hx
end Oberwolfach
