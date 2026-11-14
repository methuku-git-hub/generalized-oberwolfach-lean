module

public import Oberwolfach.FiniteSequenceWalkArcSet

@[expose] public section
/-! A union of directed walk darts also gives the corresponding unions of
ordered physical arcs and unordered physical edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem walk_edges_of_dart_union
    {V I:Type*} {G:SimpleGraph V} {a b:V}
    (q:G.Walk a b) (p:∀i:I,Σx:V,Σy:V,G.Walk x y)
    (h:∀d:G.Dart,d∈q.darts ↔ ∃i:I,d∈(p i).2.2.darts):
    ∀e:Sym2 V,e∈q.edges ↔ ∃i:I,e∈(p i).2.2.edges := by
  intro e
  simp only [SimpleGraph.Walk.edges_eq_map_darts,List.mem_map]
  constructor
  · rintro ⟨d,hd,he⟩
    obtain ⟨i,hi⟩:=(h d).mp hd
    exact ⟨i,d,hi,he⟩
  · rintro ⟨i,d,hd,he⟩
    exact ⟨d,(h d).mpr ⟨i,hd⟩,he⟩

theorem walk_physical_arcs_of_union
    {V I:Type*} [DecidableEq V] [Fintype I] {G:SimpleGraph V} {a b:V}
    (q:G.Walk a b) (p:∀i:I,Σx:V,Σy:V,G.Walk x y)
    (h:∀d:G.Dart,d∈q.darts ↔ ∃i:I,d∈(p i).2.2.darts):
    walkPhysicalArcs q=Finset.univ.biUnion (fun i=>walkPhysicalArcs (p i).2.2) := by
  ext s
  simp only [walkPhysicalArcs,List.mem_toFinset,List.mem_map,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨d,hd,heq⟩
    obtain ⟨i,hi⟩:=(h d).mp hd
    exact ⟨i,d,hi,heq⟩
  · rintro ⟨i,d,hd,heq⟩
    exact ⟨d,(h d).mpr ⟨i,hd⟩,heq⟩
end Oberwolfach
