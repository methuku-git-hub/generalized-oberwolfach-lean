module

public import Oberwolfach.PrescribedAllFreeVertices
public import Oberwolfach.PrescribedAssignedArcMatching
public import Oberwolfach.PrescribedAugmentedOccurrenceBound
public import Oberwolfach.PrescribedInsideOutsideDisjoint
public import Oberwolfach.PrescribedReservedDisjoint
public import Oberwolfach.PrescribedFamilyAvoidOldPacking

@[expose] public section
/-! Complete a family after assigning all bad edges to factors. The edge
assignment, matching property, occurrence bound and absorber avoidance are
verified in the same construction. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

theorem prescribed_assigned_family_embedding_with_image
    (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (hshape:∀ i p,p∈pieces i→p.Shape)
    (hapart:∀ i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (A:∀ i,Finset (X i)) (hA:∀ i x,x∈A i→∀ y,y∈A i→¬(prescribedDependentGraph pieces i).Adj x y)
    (f:∀ i,X i→V) (hinj:∀ i,Set.InjOn (f i) (↑(A i):Set (X i)))
    (K J:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V)
    (horient:∀e∈K.edgeFinset,prescribedArcPhysical (orient e)=e)
    (hmatching:∀i,∀e∈K.edgeFinset,∀e'∈K.edgeFinset,assign e=i→assign e'=i→e≠e'→Disjoint e.toFinset e'.toFinset)
    (Z:I→Finset V) (inner:Finset I)
    (hinner:∀i,i∈inner→prescribedAssignedArcs K assign orient i=∅)
    (houter:∀i,i∉inner→Z i=∅)
    (hOldM:∀i,Disjoint ((A i).image (f i)) (prescribedMatchingEndpoints (prescribedAssignedArcs K assign orient i)))
    (hOldZ:∀i,Disjoint ((A i).image (f i)) (Z i))
    (harc:∀i,Fintype.card (X i)≤(prescribedArcFinset (prescribedDependentDigraph pieces i)).card+(A i).card)
    (hcapacity:∀i,8*(A i).card+8*(prescribedAssignedArcs K assign orient i).card+4*(Z i).card+10≤Fintype.card (X i))
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hsize:∀i,(Fintype.card (X i):ℝ)≤δ*Fintype.card V)
    (hold:∀v,((Finset.univ.filter (fun i=>v∈(A i).image (f i))).card:ℝ)+K.degree v+
      ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀v,(J.degree v:ℝ)≤δ*Fintype.card V) (hKJ:Disjoint K.edgeFinset J.edgeFinset)
    (D Dstar:V→V→Prop) (hDD:∀ x y,D x y→Dstar x y)
    (horientTarget:∀e∈K.edgeFinset,Dstar (orient e).1 (orient e).2)
    (Pack:Finset (Sym2 V)) (hKPack:Disjoint K.edgeFinset Pack)
    (hDPack:∀x y,D x y→s(x,y)∉Pack)
    (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β):
    ∃ (B:∀ i,Finset (X i)) (g Φ:∀ i,X i→V),
      (∀i,A i⊆B i ∧ (∀x∈A i,g i x=f i x) ∧
        (B i).image (g i)=(A i).image (f i)∪prescribedMatchingEndpoints (prescribedAssignedArcs K assign orient i)∪Z i ∧
        (prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image (Prod.map (g i) (g i))=prescribedAssignedArcs K assign orient i) ∧
      (∀i,Set.InjOn (Φ i) (↑(Finset.univ:Finset (X i)):Set (X i))) ∧
      (∀i x,x∈B i→Φ i x=g i x) ∧
      (∀i v,v∈Z i→∃x,Φ i x=v) ∧
      (∀i x,x∉B i→Φ i x∈L i) ∧
      (∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
        ((x∉B i ∨ y∉B i)→D (Φ i x) (Φ i y))) ∧
      let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
      PairwisePhysicalDisjoint E ∧ K.edgeFinset⊆Finset.univ.biUnion E ∧
      (∀i,Disjoint (E i) J.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
      (∀v,(((Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1)).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) := by
  let M:=prescribedAssignedArcs K assign orient
  have hM:=prescribed_assigned_arcs_are_matchings K assign orient horient hmatching
  have hassigned:=prescribed_assigned_arcs_physical K assign orient horient
  have hsub:∀i,(M i).image prescribedArcPhysical⊆K.edgeFinset:=by
    intro i e he;exact (hassigned.1 i e he).1
  have hMZ:=prescribed_inner_outer_disjoint inner M Z hinner houter
  have hcount:∀v,((Finset.univ.filter (fun i=>v∈(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i)).card:ℝ)≤δ*Fintype.card V:=by
    intro v
    have hh:=prescribed_augmented_occurrence_bound (fun i=>(A i).image (f i)) Z M K hsub hassigned.2.2 v
    have hh':((Finset.univ.filter (fun i=>v∈(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i)).card:ℝ)≤
      ((Finset.univ.filter (fun i=>v∈(A i).image (f i))).card:ℝ)+K.degree v+
      ((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ):=by exact_mod_cast hh
    exact hh'.trans (hold v)
  have hMstar:∀i x y,(x,y)∈M i→Dstar x y:=by
    intro i x y h
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp h
    have heK:e∈K.edgeFinset:=(Finset.mem_filter.mp he).1
    have hh:=horientTarget e heK
    simpa [heq] using hh
  obtain ⟨B,g,Φ,hBg,hΦinj,hΦold,hZ,hL,hArc,hPair,hCover,hNew,hLoad,hUnion,hDegree⟩:=
    prescribed_positions_and_family_embedding_all_vertices pieces hshape hapart A hA f hinj M hM Z hOldM hOldZ hMZ
      harc hcapacity J β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hcount hJ hassigned.2.2 D Dstar hDD hMstar L hext
  have hKcover:K.edgeFinset⊆Finset.univ.biUnion (fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))):=by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨assign e,Finset.mem_univ _,hCover (assign e) (hassigned.2.1 e he)⟩
  have hJavoid:∀i,Disjoint (((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))) J.edgeFinset:=by
    intro i
    exact prescribed_edges_avoid_reserved _ _ _ (hKJ.mono (hsub i) (Finset.Subset.refl _)) (hNew i)
  have hZ':∀i v,v∈Z i→∃x,Φ i x=v:=by
    intro i v hv
    obtain ⟨x,_,hx⟩:=hZ i v hv
    exact ⟨x,hx⟩
  have hL':∀i x,x∉B i→Φ i x∈L i:=by
    intro i x hx
    exact hL i x (Finset.mem_univ x) hx
  have hBg':∀i,A i⊆B i ∧ (∀x∈A i,g i x=f i x) ∧
      (B i).image (g i)=(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i ∧
      (prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image (Prod.map (g i) (g i))=M i:=by
    intro i
    exact ⟨(hBg i).1,(hBg i).2.2.1,(hBg i).2.2.2.1,(hBg i).2.2.2.2.1⟩
  have hMPack:∀i,Disjoint ((M i).image prescribedArcPhysical) Pack:=by
    intro i;exact hKPack.mono (hsub i) (Finset.Subset.refl _)
  have hPack:=prescribed_family_avoids_old_packing pieces B g Φ hΦold M (fun i=>(hBg' i).2.2.2) D
    (fun i x y hxy hx=>(hArc i x y hxy).2 hx) Pack hMPack hDPack
  rw [prescribed_padded_free_vertices] at hLoad
  exact ⟨B,g,Φ,hBg',hΦinj,hΦold,hZ',hL',hArc,hPair,hKcover,hJavoid,hPack,hLoad,hUnion,hDegree⟩
end Oberwolfach
