module

public import Oberwolfach.ResidualPathInteriorLengths

@[expose] public section
/-! Exact remaining vertex count after deleting a disjoint set and the
interiors of pairwise disjoint paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem residual_vertex_count_from_paths (F:SimpleGraph V) (s:Finset I)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hpath:∀i∈s,(P i).IsPath) (hne:∀i∈s,u i≠v i)
    (hdisj:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (C:Finset V) (hC:∀i∈s,Disjoint C (P i).support.toFinset):
    let Z:=s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i})
    let R:=Finset.univ \ (C∪Z);
    R.card+C.card+(∑i∈s,(P i).length)=Fintype.card V+s.card := by
  let Z:=s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i})
  let R:=Finset.univ \ (C∪Z)
  have hCZ:Disjoint C Z:=by
    apply Finset.disjoint_left.mpr
    intro x hx hz
    obtain ⟨i,hi,hzi⟩:=Finset.mem_biUnion.mp hz
    exact Finset.disjoint_left.mp (hC i hi) hx (Finset.mem_sdiff.mp hzi).1
  have hcount:=disjoint_path_interiors_and_lengths F s u v P hpath hne hdisj
  have hrest:=Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (C∪Z))
  have hunion:=Finset.card_union_of_disjoint hCZ
  change R.card+C.card+(∑i∈s,(P i).length)=Fintype.card V+s.card
  rw [hunion,Finset.card_univ] at hrest
  change Z.card+s.card=(∑i∈s,(P i).length) at hcount
  change R.card+(C.card+Z.card)=Fintype.card V at hrest
  omega
end Oberwolfach
