module

public import Oberwolfach.PrescribedFamilyState
public import Oberwolfach.PrescribedActualUsedGraph
public import Oberwolfach.PrescribedSourceEdgesImage
public import Oberwolfach.PrescribedEmbeddingNumerics

@[expose] public section
/-! The union of the recorded physical images has the manuscript's degree
bound, derived from actual prescribed and free-image counts. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

def prescribedPhysicalUnion (E:I→Finset (Sym2 V)):SimpleGraph V:=
  SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion E):Set (Sym2 V))

theorem prescribed_family_physical_degree
    (st:PrescribedFamilyState I X V) (QV:I→Finset X) (Q:I→SimpleGraph X)
    (A₀:I→Finset X) (ψ:I→X→V) (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ n:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hn:2/Real.sqrt δ≤n) (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*n)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*n)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*n)):
    (prescribedPhysicalUnion st.physicalEdges).edgeFinset=Finset.univ.biUnion st.physicalEdges ∧
    ∀ v,(prescribedPhysicalUnion st.physicalEdges |>.degree v:ℝ)≤5*Real.sqrt δ*n := by
  have hfree:∀ v,((st.freeOccurrences.filter (fun p=>st.vertexMap p.1 p.2=v)).card:ℝ)≤Real.sqrt δ*n+1:=by
    intro v
    have heq:st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v) =
        st.freeOccurrences.filter (fun p=>st.vertexMap p.1 p.2=v):=by
      ext p
      simp only [familyVertexImage, Finset.mem_filter]
      exact Finset.mem_filter
    rw [←heq]
    exact hvalid.2.2.2.2.1 v
  obtain ⟨G,hG,hcontains⟩:=prescribed_actual_used_graph Q st.assigned A₀ st.vertexMap ψ st.freeOccurrences
    hvalid.1 hvalid.2.1 hvalid.2.2.2.1 hQdegree δ n (Real.sqrt δ*n) hold hfree J hJ
  have hE:∀ i,st.physicalEdges i⊆G.edgeFinset:=by
    intro i
    rw [hvalid.2.2.2.2.2.2.2.1 i]
    exact (prescribed_source_edges_image_contained (Q i) (st.assigned i) (st.vertexMap i) (hvalid.1 i)
      (st.sourceEdges i) (hvalid.2.2.2.2.2.1 i) (hvalid.2.2.2.2.2.2.1 i)).trans (hcontains i)
  have hedge:(prescribedPhysicalUnion st.physicalEdges).edgeFinset=Finset.univ.biUnion st.physicalEdges:=by
    ext e
    constructor
    · intro he
      have hh:e∈(prescribedPhysicalUnion st.physicalEdges).edgeSet:=SimpleGraph.mem_edgeFinset.mp he
      change e∈(SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion st.physicalEdges):Set (Sym2 V))).edgeSet at hh
      rw [SimpleGraph.edgeSet_fromEdgeSet] at hh
      exact hh.1
    · intro he
      obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
      have hnot:¬e.IsDiag:=G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hE i hi))
      apply SimpleGraph.mem_edgeFinset.mpr
      change e∈(SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion st.physicalEdges):Set (Sym2 V))).edgeSet
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨he,hnot⟩
  have hle:prescribedPhysicalUnion st.physicalEdges≤G:=by
    intro x y hxy
    have he:s(x,y)∈Finset.univ.biUnion st.physicalEdges:=by
      have hh: s(x,y)∈(↑(Finset.univ.biUnion st.physicalEdges):Set (Sym2 V)):=
        ((SimpleGraph.fromEdgeSet_adj _).mp hxy).1
      exact hh
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact SimpleGraph.mem_edgeFinset.mp (hE i hi)
  have hnum:=prescribed_embedding_margins_from_hypotheses β δ n hβ hβ1 hδ hδbound hn
  refine ⟨hedge,?_⟩
  intro v
  have hd:((prescribedPhysicalUnion st.physicalEdges).degree v:ℝ)≤G.degree v:=by
    exact_mod_cast SimpleGraph.degree_le_of_le hle
  have hh:=hG v
  nlinarith [hnum.2.2.1]
end Oberwolfach
