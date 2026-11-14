module

public import Oberwolfach.ResidualActualCompletedEdgeFamily
public import Oberwolfach.ResidualActualFamilyForPositions

@[expose] public section
/-! Connect the edge images of the source-piece constructor to the actual
induced residual graphs, then glue their physical edge-disjoint families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_piece_family_glued_physical_edges
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
    (hgraph:∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i)))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ h:∀i,X i→V) (Φ:∀i,{x // x∈(a i).remaining}→V)
    (hold:∀i x,x∈(a i).oldDomain→h i x=ψ i x)
    (hrem:∀i (x:{x // x∈(a i).remaining}),h i x.1=Φ i x)
    (Pack Kbad:Finset (Sym2 V))
    (hOld:PairwisePhysicalDisjoint (fun i=>((a i).deletedEdges).image (Sym2.map (ψ i))))
    (hOldPack:∀i,((a i).deletedEdges).image (Sym2.map (ψ i))⊆Pack)
    (hNew:PairwisePhysicalDisjoint (fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))))
    (hNewPack:∀i,Disjoint (((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))) Pack)
    (hK:Kbad⊆Finset.univ.biUnion (fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i)))):
    PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (h i))) ∧
    Kbad⊆Finset.univ.biUnion (fun i=>((F i).edgeFinset).image (Sym2.map (h i))) :=by
  have hEq:∀i,((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))=
      (((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i)):=by
    intro i
    congr 1
    rw [hgraph i]
    apply graph_edge_finset_instance_eq
  have hNew':PairwisePhysicalDisjoint (fun i=>(((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i))):=by
    intro i j hij
    dsimp only
    rw [←hEq i,←hEq j]
    exact hNew i j hij
  have hPack':∀i,Disjoint ((((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i))) Pack:=by
    intro i
    rw [←hEq i]
    exact hNewPack i
  have hK':Kbad⊆Finset.univ.biUnion (fun i=>(((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i))):=by
    simpa only [←hEq] using hK
  exact ⟨(actual_glued_family_physical_edge_partition F hF a hCycle ψ h Φ hold hrem Pack hOld hOldPack hNew' hPack').2,
    actual_glued_family_covers_assigned_edges F hF a hCycle ψ h Φ hold hrem Kbad hK'⟩
theorem actual_glued_factor_avoids_reserved_edges
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
    (hgraph:∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i)))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ h:∀i,X i→V) (Φ:∀i,{x // x∈(a i).remaining}→V)
    (hold:∀i x,x∈(a i).oldDomain→h i x=ψ i x)
    (hrem:∀i (x:{x // x∈(a i).remaining}),h i x.1=Φ i x)
    (Pack Reserved:Finset (Sym2 V))
    (hOldPack:∀i,((a i).deletedEdges).image (Sym2.map (ψ i))⊆Pack)
    (hPackRes:Disjoint Pack Reserved)
    (hNewRes:∀i,Disjoint (((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))) Reserved):
    ∀i,Disjoint (((F i).edgeFinset).image (Sym2.map (h i))) Reserved :=by
  intro i
  rw [(a i).glued_factor_edge_images (hF i) (hCycle i) (ψ i) (h i) (Φ i) (hold i) (hrem i)]
  apply Finset.disjoint_union_left.mpr
  refine ⟨hPackRes.mono_left (hOldPack i),?_⟩
  have heq:((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))=
      (((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i)):=by
    congr 1
    rw [hgraph i]
    apply graph_edge_finset_instance_eq
  rw [←heq]
  exact hNewRes i
end Oberwolfach
