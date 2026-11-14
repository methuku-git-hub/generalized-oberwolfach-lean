module

public import Oberwolfach.ResidualActualEdgePartition
public import Oberwolfach.PrescribedEmbeddingDisjointUpdate

@[expose] public section
/-! Physical images of the full factors after gluing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_glued_family_physical_edge_partition
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ h:∀i,X i→V) (Φ:∀i,{x // x∈(a i).remaining}→V)
    (hold:∀i x,x∈(a i).oldDomain→h i x=ψ i x)
    (hrem:∀i (x:{x // x∈(a i).remaining}),h i x.1=Φ i x)
    (Pack:Finset (Sym2 V))
    (hOld:PairwisePhysicalDisjoint (fun i=>((a i).deletedEdges).image (Sym2.map (ψ i))))
    (hOldPack:∀i,((a i).deletedEdges).image (Sym2.map (ψ i))⊆Pack)
    (hNew:PairwisePhysicalDisjoint (fun i=>(((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i))))
    (hNewPack:∀i,Disjoint ((((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i))) Pack):
    (∀i,((F i).edgeFinset).image (Sym2.map (h i))=
      ((a i).deletedEdges).image (Sym2.map (ψ i)) ∪
      (((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i))) ∧
    PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (h i))) := by
  have heq:∀i,((F i).edgeFinset).image (Sym2.map (h i))=
      ((a i).deletedEdges).image (Sym2.map (ψ i)) ∪
      (((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i)) :=by
    intro i
    exact (a i).glued_factor_edge_images (hF i) (hCycle i) (ψ i) (h i) (Φ i) (hold i) (hrem i)
  refine ⟨heq,?_⟩
  intro i j hij
  dsimp only
  rw [heq i,heq j]
  apply Finset.disjoint_union_left.mpr
  constructor
  · apply Finset.disjoint_union_right.mpr
    exact ⟨hOld i j hij,((hNewPack j).mono_right (hOldPack i)).symm⟩
  · apply Finset.disjoint_union_right.mpr
    exact ⟨(hNewPack i).mono_right (hOldPack j),hNew i j hij⟩
theorem actual_glued_family_covers_assigned_edges
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ h:∀i,X i→V) (Φ:∀i,{x // x∈(a i).remaining}→V)
    (hold:∀i x,x∈(a i).oldDomain→h i x=ψ i x)
    (hrem:∀i (x:{x // x∈(a i).remaining}),h i x.1=Φ i x)
    (Kbad:Finset (Sym2 V))
    (hK:Kbad⊆Finset.univ.biUnion (fun i=>
      (((a i).graph.induce (↑(a i).remaining:Set (X i))).edgeFinset).image (Sym2.map (Φ i)))):
    Kbad⊆Finset.univ.biUnion (fun i=>((F i).edgeFinset).image (Sym2.map (h i))) := by
  intro e he
  obtain ⟨i,hi,he⟩:=Finset.mem_biUnion.mp (hK he)
  apply Finset.mem_biUnion.mpr
  refine ⟨i,hi,?_⟩
  rw [(a i).glued_factor_edge_images (hF i) (hCycle i) (ψ i) (h i) (Φ i) (hold i) (hrem i)]
  exact Finset.mem_union_right _ he
end Oberwolfach
