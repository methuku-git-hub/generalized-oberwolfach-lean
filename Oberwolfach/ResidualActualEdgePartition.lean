module

public import Oberwolfach.ResidualActualPhysicalEdges
public import Oberwolfach.PrescribedGluedPhysicalEdges

@[expose] public section
/-! Exact source-edge partition and its image under a glued embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
  [DecidableEq K] [DecidableEq J] {F:SimpleGraph X}
theorem graph_edge_finset_instance_eq {W:Type} (G:SimpleGraph W) (A B:Fintype G.edgeSet):
    @SimpleGraph.edgeFinset W G A = @SimpleGraph.edgeFinset W G B := by
  apply Finset.coe_injective
  exact (@SimpleGraph.coe_edgeFinset W G A).trans (@SimpleGraph.coe_edgeFinset W G B).symm
namespace ActualResidualData
variable (a:ActualResidualData (K:=K) (J:=J) F)

theorem source_edge_partition:
    F.edgeFinset=a.deletedEdges∪a.graph.edgeFinset:=by
  have hsub:=a.deleted_edges_subset_factor
  have heq:a.graph.edgeFinset=F.edgeFinset\a.deletedEdges:=by
    exact SimpleGraph.edgeFinset_deleteEdges (G:=F) a.deletedEdges
  rw [heq,Finset.union_sdiff_of_subset hsub]

theorem induced_edge_image (hF:F.IsRegularOfDegree 2):
    ((a.graph.induce (↑a.remaining:Set X)).edgeFinset).image
      (Sym2.map (fun x:{x // x∈a.remaining}=>x.1))=a.graph.edgeFinset :=by
  have hs:a.graph.support⊆(↑a.remaining:Set X):=by
    intro x hx
    by_contra hn
    obtain ⟨y,hxy⟩:=a.graph.mem_support.mp hx
    exact (a.graph_facts hF).2.2.2.2.1 x hn y hxy
  have hh:=SimpleGraph.map_edgeFinset_induce_of_support_subset hs
  convert hh using 1 <;> rw [Finset.map_eq_image] <;> congr 1
  apply graph_edge_finset_instance_eq

theorem glued_factor_edge_images (hF:F.IsRegularOfDegree 2)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (ψ h:X→V) (Φ:{x // x∈a.remaining}→V)
    (hold:∀x∈a.oldDomain,h x=ψ x) (hrem:∀x,h x.1=Φ x):
    F.edgeFinset.image (Sym2.map h)=
      a.deletedEdges.image (Sym2.map ψ)∪
        (a.graph.induce (↑a.remaining:Set X)).edgeFinset.image (Sym2.map Φ) :=by
  let embed:{x // x∈a.remaining}↪X:=⟨Subtype.val,Subtype.val_injective⟩
  have he:=prescribed_glued_physical_edge_images embed a.oldDomain a.deletedEdges
    (a.graph.induce (↑a.remaining:Set X)).edgeFinset ψ h Φ hold hrem (a.deleted_edge_vertices_in_old_domain hCycle)
  change (a.deletedEdges ∪ (a.graph.induce (↑a.remaining:Set X)).edgeFinset.image
    (Sym2.map (fun x:{x // x∈a.remaining}=>x.1))).image (Sym2.map h)=_ at he
  rw [a.induced_edge_image hF,←a.source_edge_partition] at he
  exact he
end ActualResidualData
end Oberwolfach
