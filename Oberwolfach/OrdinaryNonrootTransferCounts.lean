module

public import Oberwolfach.TransferDeletionCounts

@[expose] public section
/-! Removing a root set discards at most one free-label count per vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]
  {r:ℕ} {hr:3≤r} {Q F:SimpleGraph V} {H:V→U→Prop} {v:V} {u u':U}

theorem ordinary_transfer_excluded_vertices_loss (T:Finset V):
    (∑ C:OrdinaryTransferConfiguration hr Q F H v u u',
      if ∃z∈T,z∈Set.range C.labels then (1:ℝ) else 0)≤
      (T.card:ℝ)*(r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1):=by
  let M:ℝ:=(r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1)
  have hp (C:OrdinaryTransferConfiguration hr Q F H v u u'):
      (if ∃z∈T,z∈Set.range C.labels then (1:ℝ) else 0)≤
        ∑z∈T,if z∈Set.range C.labels then (1:ℝ) else 0:=by
    by_cases hb:∃z∈T,z∈Set.range C.labels
    · rw [if_pos hb]
      obtain ⟨z,hz,hzC⟩:=hb
      have hs:=Finset.single_le_sum (s:=T) (a:=z)
        (f:=fun z=>if z∈Set.range C.labels then (1:ℝ) else 0)
        (fun z _=>by split_ifs <;> norm_num) hz
      simpa only [hzC,ite_true] using hs
    · rw [if_neg hb]
      exact Finset.sum_nonneg (fun z _=>by split_ifs <;> norm_num)
  calc
    _ ≤ ∑ C:OrdinaryTransferConfiguration hr Q F H v u u',
        ∑z∈T,if z∈Set.range C.labels then (1:ℝ) else 0:=Finset.sum_le_sum (fun C _=>hp C)
    _ = ∑z∈T,∑ C:OrdinaryTransferConfiguration hr Q F H v u u',
        if z∈Set.range C.labels then (1:ℝ) else 0:=by rw [Finset.sum_comm]
    _ ≤ ∑_z∈T,M:=Finset.sum_le_sum (fun z _=>transfer_free_vertex_count z)
    _ = _:=by simp [M];ring
end Oberwolfach
