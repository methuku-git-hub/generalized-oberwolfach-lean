module

public import Oberwolfach.PrescribedDependentPositionFamily
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

theorem prescribed_positions_and_family_embedding
    (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (hshape:∀ i p,p∈pieces i→p.Shape)
    (hapart:∀ i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hcover:∀ i x,x∈prescribedDependentVertices pieces i)
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
    (hsize:∀ i,((prescribedDependentVertices pieces i).card:ℝ)≤δ*Fintype.card V)
    (hold:∀ v,((Finset.univ.filter (fun i=>v∈(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hpair:PairwisePhysicalDisjoint (fun i=>(M i).image prescribedArcPhysical))
    (D Dstar:V→V→Prop) (hDD:∀ x y,D x y→Dstar x y)
    (hMstar:∀ i x y,(x,y)∈M i→Dstar x y)
    (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β):
    ∃ (B:∀ i,Finset (X i)) (g Φ:∀ i,X i→V),
      (∀ i,A i⊆B i ∧ Set.InjOn (g i) (↑(B i):Set (X i)) ∧ (∀x∈A i,g i x=f i x) ∧
        (B i).image (g i)=(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i ∧
        (prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image (Prod.map (g i) (g i))=M i ∧
        prescribedDependentInitialEdges pieces B g i=(M i).image prescribedArcPhysical) ∧
      (∀ i,Set.InjOn (Φ i) (↑(prescribedDependentVertices pieces i):Set (X i))) ∧
      (∀ i x,x∈B i→Φ i x=g i x) ∧
      (∀ i v,v∈Z i→∃ x,x∈prescribedDependentVertices pieces i ∧ Φ i x=v) ∧
      (∀ i x,x∈prescribedDependentVertices pieces i→x∉B i→Φ i x∈L i) ∧
      (∀ i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
        ((x∉B i ∨ y∉B i)→D (Φ i x) (Φ i y))) ∧
      let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
      PairwisePhysicalDisjoint E ∧
      (∀ i,(M i).image prescribedArcPhysical⊆E i) ∧
      (∀ i,Disjoint (E i\(M i).image prescribedArcPhysical) J.edgeFinset) ∧
      (∀ v,(((prescribedDependentFreeVertices pieces B).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
      (∀ v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) := by
  obtain ⟨B,g,hBg⟩:=prescribed_dependent_position_family pieces hshape hapart A hA f hinj M hM Z hOldM hOldZ hMZ harc hcapacity
  have hBinj:∀ i,Set.InjOn (g i) (↑(B i):Set (X i)):=fun i=>(hBg i).2.1
  have hBsub:∀ i,B i⊆prescribedDependentVertices pieces i:=by intro i x hx;exact hcover i x
  have hE:∀ i,prescribedDependentInitialEdges pieces B g i=(M i).image prescribedArcPhysical:=fun i=>(hBg i).2.2.2.2.2
  have hpair':PairwisePhysicalDisjoint (prescribedDependentInitialEdges pieces B g):=by
    have heq:prescribedDependentInitialEdges pieces B g=(fun i=>(M i).image prescribedArcPhysical):=funext hE
    rw [heq];exact hpair
  have hold':∀ v,((Finset.univ.filter (fun i=>∃ x,x∈B i ∧ g i x=v)).card:ℝ)≤δ*Fintype.card V:=by
    intro v
    have hf:(Finset.univ.filter (fun i=>∃ x,x∈B i ∧ g i x=v))=
        Finset.univ.filter (fun i=>v∈(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i):=by
      apply Finset.filter_congr
      intro i _
      rw [←(hBg i).2.2.2.1]
      exact (Finset.mem_image).symm
    rw [hf];exact hold v
  have hpres:∀ i x y,prescribedDependentDigraph pieces i x y→x∈B i→y∈B i→Dstar (g i x) (g i y):=by
    intro i x y hxy hx hy
    apply hMstar i (g i x) (g i y)
    rw [←(hBg i).2.2.2.2.1]
    apply Finset.mem_image.mpr
    refine ⟨(x,y),?_,rfl⟩
    simp [prescribedInducedArcs,hx,hy,hxy]
  obtain ⟨Φ,hΦinj,hΦold,hΦL,hΦarc,hΦpair,hΦJ,hΦload,hΦunion,hΦdegree⟩:=
    prescribed_dependent_family_embedding pieces hshape hapart B g J β δ hβ hβ1 hδ hδbound hnβ hn hI hsize hold' hJ hBinj hBsub hpair' D Dstar hDD hpres L hext
  have hMcover:∀ i,(M i).image prescribedArcPhysical⊆((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i)):=by
    intro i
    rw [←hE i]
    unfold prescribedDependentInitialEdges
    intro e he
    obtain ⟨a,ha,hae⟩:=Finset.mem_image.mp he
    have haQ:a∈(prescribedDependentGraph pieces i).edgeFinset:=(Finset.mem_filter.mp ha).1
    have haeq:Sym2.map (g i) a=Sym2.map (Φ i) a:=by
      induction a using Sym2.ind with
      | _ x y =>
        have hh: (prescribedDependentGraph pieces i).Adj x y ∧ x∈B i ∧ y∈B i:=
          (prescribed_induced_edge_mk (prescribedDependentGraph pieces i) (B i) x y).mp ha
        change s(g i x,g i y)=s(Φ i x,Φ i y)
        rw [hΦold i x hh.2.1,hΦold i y hh.2.2]
    exact Finset.mem_image.mpr ⟨a,haQ,haeq.symm.trans hae⟩
  have hZcover:∀ i v,v∈Z i→∃ x,x∈prescribedDependentVertices pieces i ∧ Φ i x=v:=by
    intro i v hv
    have hvi:v∈(B i).image (g i):=by
      rw [(hBg i).2.2.2.1]
      exact Finset.mem_union_right _ hv
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hvi
    exact ⟨x,hcover i x,(hΦold i x hx).trans hxv⟩
  refine ⟨B,g,Φ,?_,hΦinj,hΦold,hZcover,hΦL,hΦarc,hΦpair,hMcover,?_,hΦload,hΦunion,hΦdegree⟩
  · intro i
    have hh:=hBg i
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2⟩
  · intro i
    simpa only [hE i] using hΦJ i
end Oberwolfach
