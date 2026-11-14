module

public import Oberwolfach.FiniteSequenceWalkEdgeSet

@[expose] public section
/-! Edge membership in a concatenated walk gives the corresponding union
of physical edge sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem walk_physical_edges_of_union
    {V I:Type*} [DecidableEq V] [Fintype I] {G:SimpleGraph V} {a b:V}
    (q:G.Walk a b) (p:∀i:I,Σx:V,Σy:V,G.Walk x y)
    (h:∀e:Sym2 V,e∈q.edges ↔ ∃i:I,e∈(p i).2.2.edges):
    walkPhysicalEdges q=Finset.univ.biUnion (fun i=>walkPhysicalEdges (p i).2.2) := by
  ext s
  simp only [walkPhysicalEdges,List.mem_toFinset,List.mem_map,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,heq⟩
    obtain ⟨i,hi⟩:=(h e).mp he
    exact ⟨i,e,hi,heq⟩
  · rintro ⟨i,e,he,heq⟩
    exact ⟨e,(h e).mpr ⟨i,he⟩,heq⟩
end Oberwolfach
