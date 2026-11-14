module

public import Oberwolfach.PrescribedFamilyEmbeddingFromComponents
public import Oberwolfach.PrescribedOriginalSourcePieces

@[expose] public section
/-! The prescribed family theorem for ordinary directed path-and-cycle
components, without any forbidden-source graph. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_embedding_original_components
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hinj:FamilyPartialInjections A₀ ψ) (hA:∀ i,A₀ i⊆QV i)
    (hE₀:∀ i,E₀ i=(prescribedInducedSourceEdges (Q i) (A₀ i)).image (Sym2.map (ψ i)))
    (hpair:PairwisePhysicalDisjoint E₀)
    (Dsrc:I→X→X→Prop) (hDQ:∀ i x y,Dsrc i x y→(Q i).Adj x y)
    (D Dstar:V→V→Prop) (hDD:∀ x y,D x y→Dstar x y)
    (hpresArc:∀ i x y,Dsrc i x y→x∈A₀ i→y∈A₀ i→Dstar (ψ i x) (ψ i y))
    (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β)
    (ps:List (I×PrescribedSourcePiece X))
    (hpieces:∀ p∈ps,p.2.OriginalValid (Dsrc p.1))
    (hapart:ps.Pairwise PrescribedPiecesApart)
    (hsubset:∀ p∈ps,∀ x∈p.2.vertices,x∈QV p.1)
    (hcoverV:∀ i x,x∈QV i→∃ p∈ps,p.1=i ∧ x∈p.2.vertices)
    (hcoverE:∀ i e,e∈(Q i).edgeFinset→∃ p∈ps,p.1=i ∧ e∈p.2.edges)
    (hcoverA:∀ i x y,Dsrc i x y→∃ p∈ps,p.1=i ∧ (x,y)∈p.2.arcs):
    ∃ st:PrescribedFamilyState I X V,
      st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀ i,st.assigned i=QV i) ∧ (∀ i,st.sourceEdges i=(Q i).edgeFinset) ∧
      (∀ i,Set.InjOn (st.vertexMap i) (↑(QV i):Set X)) ∧
      (∀ i x,x∈A₀ i→st.vertexMap i x=ψ i x) ∧
      (∀ i x,x∈QV i→x∉A₀ i→st.vertexMap i x∈L i) ∧
      (∀ i x y,Dsrc i x y→Dstar (st.vertexMap i x) (st.vertexMap i y) ∧
        ((x∉A₀ i ∨ y∉A₀ i)→D (st.vertexMap i x) (st.vertexMap i y))) ∧
      (∀ i,st.physicalEdges i=((Q i).edgeFinset).image (Sym2.map (st.vertexMap i))) ∧
      PairwisePhysicalDisjoint st.physicalEdges ∧
      (∀ i,Disjoint (st.physicalEdges i\E₀ i) J.edgeFinset) ∧
      (∀ v,(((prescribedFreeSourceOccurrences QV A₀).filter
        (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion st.physicalEdges).edgeFinset=Finset.univ.biUnion st.physicalEdges ∧
      (∀ v,((prescribedPhysicalUnion st.physicalEdges).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) := by
  have hpieces':∀ p∈ps,p.2.Valid (Dsrc p.1) ⊥:=by
    intro p hp
    exact prescribed_original_piece_valid p.2 (Dsrc p.1) (hpieces p hp)
  exact prescribed_family_embedding_from_components QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
    hQsize hold hJ hinj hA hE₀ hpair Dsrc (fun _=>⊥) hDQ D Dstar hDD hpresArc L hext ps
    hpieces' hapart hsubset hcoverV hcoverE hcoverA
end Oberwolfach
