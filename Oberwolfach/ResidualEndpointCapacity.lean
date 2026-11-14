module

public import Oberwolfach.ResidualDeletionGraph

@[expose] public section
/-! Disjoint deleted paths have distinct initial endpoints, so any set
containing those endpoints has at least as many vertices as deleted paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem disjoint_walk_startpoints_card_le (F:SimpleGraph V) (s:Finset I)
    (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (A:Finset V) (hA:∀i∈s,u i∈A):s.card≤A.card := by
  have hinj:Set.InjOn u s := by
    intro i hi j hj heq
    by_contra hne
    have hi' : u i∈(P i).support.toFinset := by simp
    have hj' : u i∈(P j).support.toFinset := by simpa [heq] using (P j).start_mem_support
    exact Finset.disjoint_left.mp (hP hi hj hne) hi' hj'
  have hsub:s.image u⊆A := by
    intro x hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    exact hA i hi
  rw [←Finset.card_image_iff.mpr hinj]
  exact Finset.card_le_card hsub
end Oberwolfach
