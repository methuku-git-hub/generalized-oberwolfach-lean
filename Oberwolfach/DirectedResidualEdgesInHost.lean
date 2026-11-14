module

public import Oberwolfach.PrescribedFamilyAvoidOldPacking
public import Oberwolfach.ResidualActualData

@[expose] public section
/-! A directed residual embedding places its underlying physical edges in
the host, whenever every permitted target arc is a host edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem directed_source_edge_images_subset_host
    {X V:Type*} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
    (Q:SimpleGraph X) (H:SimpleGraph V) (R:X→X→Prop) (f:X→V)
    (hrep:∀x y,Q.Adj x y→R x y∨R y x)
    (harc:∀x y,R x y→H.Adj (f x) (f y)) :
    Q.edgeFinset.image (Sym2.map f)⊆H.edgeFinset := by
  classical
  intro e he
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
  induction a using Sym2.inductionOn with
  | _ x y =>
    have hxy:Q.Adj x y:=by simpa using ha
    apply SimpleGraph.mem_edgeFinset.mpr
    rcases hrep x y hxy with h|h
    · exact harc x y h
    · exact (harc y x h).symm

theorem actual_residual_directed_new_edges_subset_host
    {I X V K J:Type} [Fintype I] [Fintype X] [Fintype V]
    [DecidableEq I] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    (F:I→SimpleGraph X) (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
    (hgraph:∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set X))
    (H:SimpleGraph V) (Dstar:V→V→Prop) (hHost:∀x y,Dstar x y→H.Adj x y)
    (Φ:∀i,{x // x∈(a i).remaining}→V)
    (harc:∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y)) :
    ∀i,(((a i).graph.induce (↑(a i).remaining:Set X)).edgeFinset).image
      (Sym2.map (Φ i))⊆H.edgeFinset := by
  intro i e he
  obtain ⟨z,hz,heq⟩:=Finset.mem_image.mp he
  induction z using Sym2.inductionOn with
  | _ x y =>
    have hxy:((a i).graph.induce (↑(a i).remaining:Set X)).Adj x y:=SimpleGraph.mem_edgeFinset.mp hz
    have hxy':(prescribedDependentGraph pieces i).Adj x y:=by rw [hgraph i];exact hxy
    have hor:=prescribed_dependent_source_representation pieces i x y hxy'
    have hed:Sym2.map (Φ i) s(x,y)∈H.edgeFinset:=by
      change s(Φ i x,Φ i y)∈H.edgeFinset
      apply SimpleGraph.mem_edgeFinset.mpr
      rcases hor with h|h
      · exact hHost _ _ (harc i x y h)
      · exact (hHost _ _ (harc i y x h)).symm
    exact heq ▸ hed
end Oberwolfach
