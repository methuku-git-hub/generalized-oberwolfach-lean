module

public import Oberwolfach.ResidualDisjointPathCount

@[expose] public section
/-! Count the internal vertices of a disjoint family of simple paths in
terms of their lengths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem disjoint_path_interiors_and_lengths (F:SimpleGraph V) (s:Finset I)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hpath:∀i∈s,(P i).IsPath) (hne:∀i∈s,u i≠v i)
    (hdisj:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset)):
    (s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i})).card+s.card=
      ∑i∈s,(P i).length := by
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
  rw [←disjoint_simple_paths_edges_and_internal_vertices F s u v P hpath hne hdisj,
    Finset.card_biUnion he]
  apply Finset.sum_congr rfl
  intro i hi
  rw [List.toFinset_card_of_nodup (hpath i hi).isTrail.edges_nodup,(P i).length_edges]
end Oberwolfach
