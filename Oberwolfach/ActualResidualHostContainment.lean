module

public import Oberwolfach.ResidualActualCompletedPieceFamily
public import Oberwolfach.PrescribedFamilyAvoidOldPacking

@[expose] public section
/-! Directed source-piece embeddings into a host give physical-edge
containment for the whole glued factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem prescribed_piece_images_in_host
    (F:∀i,SimpleGraph (X i)) (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
    (Φ:∀i,{x // x∈(a i).remaining}→V) (Dstar:V→V→Prop)
    (harc:∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y))
    (G:SimpleGraph V) (hhost:∀x y,Dstar x y→G.Adj x y):
    ∀i,((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))⊆G.edgeFinset :=by
  intro i e he
  obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp he
  induction s using Sym2.ind with
  | _ x y =>
    have hxy:(prescribedDependentGraph pieces i).Adj x y:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hs
    obtain h|h:=prescribed_dependent_source_representation pieces i x y hxy
    · have hg:=hhost (Φ i x) (Φ i y) (harc i x y h)
      simpa only [Sym2.map_mk,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hg
    · have hg: G.Adj (Φ i x) (Φ i y):=(hhost (Φ i y) (Φ i x) (harc i y x h)).symm
      simpa only [Sym2.map_mk,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hg

theorem actual_glued_factor_images_in_host
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
    (hgraph:∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i)))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ h:∀i,X i→V) (Φ:∀i,{x // x∈(a i).remaining}→V)
    (hold:∀i x,x∈(a i).oldDomain→h i x=ψ i x)
    (hrem:∀i (x:{x // x∈(a i).remaining}),h i x.1=Φ i x)
    (Dstar:V→V→Prop) (harc:∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y))
    (Pack:Finset (Sym2 V)) (hOldPack:∀i,((a i).deletedEdges).image (Sym2.map (ψ i))⊆Pack)
    (G:SimpleGraph V) (hPackHost:Pack⊆G.edgeFinset) (hhost:∀x y,Dstar x y→G.Adj x y):
    ∀i,((F i).edgeFinset).image (Sym2.map (h i))⊆G.edgeFinset :=by
  have hnew:=prescribed_piece_images_in_host F a pieces Φ Dstar harc G hhost
  intro i
  rw [(a i).glued_factor_edge_images (hF i) (hCycle i) (ψ i) (h i) (Φ i) (hold i) (hrem i)]
  apply Finset.union_subset
  · exact (hOldPack i).trans hPackHost
  · convert hnew i using 1
    congr 1
    rw [hgraph i]
    apply graph_edge_finset_instance_eq
end Oberwolfach
