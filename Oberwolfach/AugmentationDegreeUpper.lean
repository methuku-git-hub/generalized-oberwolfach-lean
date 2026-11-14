module

public import Oberwolfach.TriangleTransformerFactors

@[expose] public section
/-! Removing edges and the bounded old set changes each degree by at most
its size, including at vertices outside the new set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem augmentation_degree_upper {V:Type} [Fintype V] [DecidableEq V]
    (G D:SimpleGraph V) (S:Finset V) (v:V):
    (triangleAugmentationGraph G D S).degree v≤(G.neighborFinset v∩S).card+(Fintype.card V-S.card):=by
  have hsub:(triangleAugmentationGraph G D S).neighborFinset v⊆
      (G.neighborFinset v∩S)∪(Finset.univ\S):=by
    intro w hw
    have hg:G.Adj v w:=(show (triangleAugmentationGraph G D S).Adj v w from by simpa using hw).1
    by_cases hws:w∈S
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨by simpa using hg,hws⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hws⟩)
  have hcard:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ] using hcard
end Oberwolfach
