module

public import Oberwolfach.PrescribedPositionsRestrictedEmbedding
public import Oberwolfach.PrescribedPositionsEmbeddingCombined
public import Oberwolfach.PrescribedSourceSingletonPadding
public import Oberwolfach.PrescribedDependentEmbedding

@[expose] public section
/-! Prescribe all matching endpoints and isolated labels, then embed the
remaining source factors with the original family embedding theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

theorem prescribed_positions_and_family_restricted_embedding_all_vertices
    (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (hshape:∀ i p,p∈pieces i→p.Shape)
    (hapart:∀ i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (A:∀ i,Finset (X i)) (hA:∀ i x,x∈A i→∀ y,y∈A i→¬(prescribedDependentGraph pieces i).Adj x y)
    (f:∀ i,X i→V) (hinj:∀ i,Set.InjOn (f i) (↑(A i):Set (X i)))
    (M:I→Finset (V×V)) (hM:∀ i,IsPrescribedOrientedMatching (M i)) (Z:I→Finset V)
    (hOldM:∀ i,Disjoint ((A i).image (f i)) (prescribedMatchingEndpoints (M i)))
    (hOldZ:∀ i,Disjoint ((A i).image (f i)) (Z i))
    (hMZ:∀ i,Disjoint (prescribedMatchingEndpoints (M i)) (Z i))
    (harc:∀ i,Fintype.card (X i)≤(prescribedArcFinset (prescribedDependentDigraph pieces i)).card+(A i).card)
    (hcapacity:∀ i,8*(A i).card+8*(M i).card+4*(Z i).card+10≤Fintype.card (X i))
    (J:SimpleGraph V) (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hsize:∀ i,(Fintype.card (X i):ℝ)≤δ*Fintype.card V)
    (hold:∀ v,((Finset.univ.filter (fun i=>v∈(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hpair:PairwisePhysicalDisjoint (fun i=>(M i).image prescribedArcPhysical))
    (D Dstar:V→V→Prop) (hDD:∀ x y,D x y→Dstar x y)
    (hMstar:∀ i x y,(x,y)∈M i→Dstar x y)
    (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β)
    (H:Finset I) (aScale κ θ:ℝ) (haScale:0<aScale) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤aScale) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,(Fintype.card (X i):ℝ)≤θ*Fintype.card V)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ)):
    ∃ (B:∀ i,Finset (X i)) (g Φ:∀ i,X i→V),
      (∀ i,A i⊆B i ∧ Set.InjOn (g i) (↑(B i):Set (X i)) ∧ (∀x∈A i,g i x=f i x) ∧
        (B i).image (g i)=(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i ∧
        (prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image (Prod.map (g i) (g i))=M i ∧
        prescribedDependentInitialEdges pieces B g i=(M i).image prescribedArcPhysical) ∧
      (∀ i,Set.InjOn (Φ i) (↑(Finset.univ:Finset (X i)):Set (X i))) ∧
      (∀ i x,x∈B i→Φ i x=g i x) ∧
      (∀ i v,v∈Z i→∃ x,x∈(Finset.univ:Finset (X i)) ∧ Φ i x=v) ∧
      (∀ i x,x∈(Finset.univ:Finset (X i))→x∉B i→Φ i x∈L i) ∧
      (∀ i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
        ((x∉B i ∨ y∉B i)→D (Φ i x) (Φ i y))) ∧
      let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
      PairwisePhysicalDisjoint E ∧
      (∀ i,(M i).image prescribedArcPhysical⊆E i) ∧
      (∀ i,Disjoint (E i\(M i).image prescribedArcPhysical) J.edgeFinset) ∧
      (∀ v,(((prescribedDependentFreeVertices (prescribedPadSingletons pieces) B).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
      (∀ v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) ∧
      (∀v,((((prescribedDependentFreeVertices (prescribedPadSingletons pieces) B).filter (fun z=>z.1∈H)).filter
        (fun z=>Φ z.1 z.2=v)).card:ℝ)≤κ*aScale+1) := by
  let padded:=prescribedPadSingletons pieces
  have hshape':∀ i p,p∈padded i→p.Shape:=prescribed_padding_shape pieces hshape
  have hapart':∀ i,(padded i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset):=prescribed_padding_apart pieces hapart
  have hcover':∀ i x,x∈prescribedDependentVertices padded i:=by
    intro i x
    rw [prescribed_padding_vertices]
    exact Finset.mem_univ x
  have hA':∀ i x,x∈A i→∀ y,y∈A i→¬(prescribedDependentGraph padded i).Adj x y:=by
    simpa only [padded,prescribed_padding_graph] using hA
  have harc':∀ i,Fintype.card (X i)≤(prescribedArcFinset (prescribedDependentDigraph padded i)).card+(A i).card:=by
    simpa only [padded,prescribed_padding_digraph] using harc
  have hsize':∀ i,((prescribedDependentVertices padded i).card:ℝ)≤δ*Fintype.card V:=by
    intro i
    simpa only [padded,prescribed_padding_vertices,Finset.card_univ] using hsize i
  have hQlocal':∀i∈H,((prescribedDependentVertices padded i).card:ℝ)≤θ*Fintype.card V:=by
    intro i hi
    simpa only [padded,prescribed_padding_vertices,Finset.card_univ] using hQlocal i hi
  have hh:=prescribed_positions_and_family_restricted_embedding padded hshape' hapart' hcover' A hA' f hinj M hM Z
    hOldM hOldZ hMZ harc' hcapacity J β δ hβ hβ1 hδ hδbound hnβ hn hI hsize' hold hJ hpair D Dstar hDD hMstar L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal' hδstrong hnstrong
  obtain ⟨B,g,Φ,hBg,hΦinj,hΦold,hZ,hL,hArc,hPair,hMCover,hJavoid,hLoad,hUnion,hDegree,hRestricted⟩:=hh
  simp only [padded,prescribedDependentInitialEdges,prescribed_padding_graph,prescribed_padding_digraph] at hBg
  simp only [padded,prescribed_padding_vertices] at hΦinj hZ hL
  simp only [padded,prescribed_padding_digraph] at hArc
  simp only [padded] at hPair hMCover hJavoid hUnion hDegree
  have hgraphfun:prescribedDependentGraph (prescribedPadSingletons pieces)=prescribedDependentGraph pieces:=funext (prescribed_padding_graph pieces)
  rw [hgraphfun] at hPair hMCover hJavoid hUnion hDegree
  exact ⟨B,g,Φ,hBg,hΦinj,hΦold,hZ,hL,hArc,hPair,hMCover,hJavoid,hLoad,hUnion,hDegree,hRestricted⟩
end Oberwolfach
