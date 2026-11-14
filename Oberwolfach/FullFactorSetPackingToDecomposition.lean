module

public import Oberwolfach.TwoFactorEmbeddingDecomposition
public import Oberwolfach.PartialFactorWalkEdgeDisjointnessPoly

@[expose] public section
/-! Transfer completed embeddings with set-valued physical edge disjointness
to the exact spanning-factor decomposition interface. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mapped_edge_finset_mem_physical_set
    {X Y:Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (F:SimpleGraph X) (f:X→Y) (e:Sym2 Y)
    (he:e∈F.edgeFinset.image (Sym2.map f)) : e∈partialFactorPhysicalEdgesPoly X F f := by
  classical
  obtain ⟨a,ha,heq⟩:=Finset.mem_image.mp he
  induction a using Sym2.inductionOn with
  | _ x y =>
    have hxy:F.Adj x y:=by simpa using ha
    refine ⟨x,y,hxy,?_⟩
    simpa using heq.symm

theorem completed_two_factor_set_packing_gives_decomposition {n D:ℕ}
    (hEven:Even D) (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree D)
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (f:Fin (D/2)→Fin n↪Fin n)
    (hgraph:∀i x y,(F i).Adj x y→G.Adj (f i x) (f i y))
    (hdis:∀i j,i≠j→Disjoint (partialFactorPhysicalEdgesPoly (Fin n) (F i) (f i))
      (partialFactorPhysicalEdgesPoly (Fin n) (F j) (f j))) :
    HasFactorDecomposition G F := by
  classical
  apply even_regular_two_factor_embeddings_give_decomposition hEven G hG F hF (fun i=>f i) (fun i=>(f i).injective)
  · intro i e he
    obtain ⟨x,y,hxy,heq⟩:=mapped_edge_finset_mem_physical_set (F i) (f i) e he
    rw [heq]
    exact SimpleGraph.mem_edgeFinset.mpr (hgraph i x y hxy)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact (Set.disjoint_left.mp (hdis i j hij))
      (mapped_edge_finset_mem_physical_set (F i) (f i) e hi)
      (mapped_edge_finset_mem_physical_set (F j) (f j) e hj)
end Oberwolfach
