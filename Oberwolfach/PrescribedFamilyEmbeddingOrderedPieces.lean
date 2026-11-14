module

public import Oberwolfach.PrescribedFamilyEmbeddingOriginalComponents
public import Oberwolfach.PrescribedPieceSourceModel

@[expose] public section
/-! Embedding prescribed unions of ordered directed paths, isolated vertices
and cycles. Source vertices, arcs and physical edges are defined by the pieces. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_embedding_from_ordered_pieces
    (ps:List (I×PrescribedSourcePiece X))
    (hshape:∀ p∈ps,p.2.Shape) (hapart:ps.Pairwise PrescribedPiecesApart)
    (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,(((prescribedSourceVertices ps) i).card:ℝ)≤δ*Fintype.card V)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hinj:FamilyPartialInjections A₀ ψ) (hA:∀ i,A₀ i⊆(prescribedSourceVertices ps) i)
    (hE₀:∀ i,E₀ i=(prescribedInducedSourceEdges ((prescribedSourceGraph ps) i) (A₀ i)).image (Sym2.map (ψ i)))
    (hpair:PairwisePhysicalDisjoint E₀)
    (D Dstar:V→V→Prop) (hDD:∀ x y,D x y→Dstar x y)
    (hpresArc:∀ i x y,(prescribedSourceDigraph ps) i x y→x∈A₀ i→y∈A₀ i→Dstar (ψ i x) (ψ i y))
    (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β)
:
    ∃ st:PrescribedFamilyState I X V,
      st.Valid (prescribedSourceVertices ps) (prescribedSourceGraph ps) A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀ i,st.assigned i=(prescribedSourceVertices ps) i) ∧ (∀ i,st.sourceEdges i=((prescribedSourceGraph ps) i).edgeFinset) ∧
      (∀ i,Set.InjOn (st.vertexMap i) (↑((prescribedSourceVertices ps) i):Set X)) ∧
      (∀ i x,x∈A₀ i→st.vertexMap i x=ψ i x) ∧
      (∀ i x,x∈(prescribedSourceVertices ps) i→x∉A₀ i→st.vertexMap i x∈L i) ∧
      (∀ i x y,(prescribedSourceDigraph ps) i x y→Dstar (st.vertexMap i x) (st.vertexMap i y) ∧
        ((x∉A₀ i ∨ y∉A₀ i)→D (st.vertexMap i x) (st.vertexMap i y))) ∧
      (∀ i,st.physicalEdges i=(((prescribedSourceGraph ps) i).edgeFinset).image (Sym2.map (st.vertexMap i))) ∧
      PairwisePhysicalDisjoint st.physicalEdges ∧
      (∀ i,Disjoint (st.physicalEdges i\E₀ i) J.edgeFinset) ∧
      (∀ v,(((prescribedFreeSourceOccurrences (prescribedSourceVertices ps) A₀).filter
        (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion st.physicalEdges).edgeFinset=Finset.univ.biUnion st.physicalEdges ∧
      (∀ v,((prescribedPhysicalUnion st.physicalEdges).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) := by
  have hpieces:=prescribed_source_model_piece_valid ps hshape
  have hDQ:=prescribed_source_model_arc_graph ps hshape
  have hsubset:∀ p∈ps,∀ x∈p.2.vertices,x∈prescribedSourceVertices ps p.1:=by
    intro p hp x hx
    apply (prescribed_source_model_vertices ps p.1 x).mpr
    exact ⟨p,hp,rfl,hx⟩
  have hcoverV:∀ i x,x∈prescribedSourceVertices ps i→∃ p∈ps,p.1=i ∧ x∈p.2.vertices:=by
    intro i x hx;exact (prescribed_source_model_vertices ps i x).mp hx
  have hcoverE:∀ i e,e∈(prescribedSourceGraph ps i).edgeFinset→∃ p∈ps,p.1=i ∧ e∈p.2.edges:=by
    intro i e he;exact prescribed_source_model_edges ps i e he
  have hcoverA:∀ i x y,prescribedSourceDigraph ps i x y→∃ p∈ps,p.1=i ∧ (x,y)∈p.2.arcs:=by
    intro i x y h;exact h
  exact prescribed_family_embedding_original_components (prescribedSourceVertices ps) (prescribedSourceGraph ps)
    A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI hQsize hold hJ hinj hA hE₀ hpair
    (prescribedSourceDigraph ps) hDQ D Dstar hDD hpresArc L hext ps hpieces hapart hsubset hcoverV hcoverE hcoverA
end Oberwolfach
