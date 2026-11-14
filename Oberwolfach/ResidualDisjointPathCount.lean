module

public import Oberwolfach.ResidualSimplePathCount

@[expose] public section
/-! Count the union of vertex-disjoint deleted paths, preserving endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem disjoint_simple_paths_edges_and_internal_vertices
    (F:SimpleGraph V) (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hpath:∀i∈s,(P i).IsPath) (hne:∀i∈s,u i≠v i)
    (hdisj:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset)):
    (s.biUnion (fun i=>(P i).edges.toFinset)).card =
      (s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i})).card+s.card := by
  have hv : (↑s:Set I).PairwiseDisjoint
      (fun i=>(P i).support.toFinset \ {u i,v i}) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have he : (↑s:Set I).PairwiseDisjoint (fun i=>(P i).edges.toFinset) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with
    | _ x y =>
      have hxi : x∈(P i).support.toFinset := by
        apply List.mem_toFinset.mpr
        exact (P i).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hei)
      have hxj : x∈(P j).support.toFinset := by
        apply List.mem_toFinset.mpr
        exact (P j).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hej)
      exact Finset.disjoint_left.mp (hdisj hi hj hij) hxi hxj
  calc
    _ = ∑ i∈s,(P i).edges.toFinset.card := Finset.card_biUnion he
    _ = ∑ i∈s,(((P i).support.toFinset \ {u i,v i}).card+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact simple_path_edges_and_internal_vertices F (P i) (hpath i hi) (hne i hi)
    _ = _ := by rw [Finset.card_biUnion hv]; simp [Finset.sum_add_distrib]
end Oberwolfach
