module

public import Oberwolfach.ResidualGraphPositionBudget

@[expose] public section
/-! Deleting interiors keeps both endpoints of every selected path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem disjoint_deleted_path_endpoints_survive (F:SimpleGraph V)
    (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (t:Finset J) (root:J→V) (C:∀ j,F.Walk (root j) (root j))
    (hcross:∀i∈s,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset):
    ∀i∈s,∀x∈({u i,v i}:Finset V),
      x∉(t.biUnion (fun j=>(C j).support.toFinset)) ∪
        (s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i})) := by
  intro i hi x hx hdel
  have hxin:x∈(P i).support.toFinset := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl <;> simp
  rcases Finset.mem_union.mp hdel with hc|hp
  · obtain ⟨j,hj,hj'⟩:=Finset.mem_biUnion.mp hc
    exact Finset.disjoint_left.mp (hcross i hi j hj) hxin hj'
  · obtain ⟨j,hj,hj'⟩:=Finset.mem_biUnion.mp hp
    by_cases hij:i=j
    · subst j
      exact (Finset.mem_sdiff.mp hj').2 hx
    · exact Finset.disjoint_left.mp (hP hi hj hij) hxin (Finset.mem_sdiff.mp hj').1
end Oberwolfach
