module

public import Oberwolfach.ActualOldPiecePaths

@[expose] public section
/-! Neither a selected run nor a selected component cycle meets a final-path
interior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_piece_paths_avoid_final_interiors
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G):
    Disjoint (Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))
      data.additionalSelectedInteriors:=by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨z,_,hz⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hy
  have hifull:x∈(data.path (.inl i)).support.toFinset:=(Finset.mem_sdiff.mp hi).1
  cases z with
  | inl j =>
    have hj:x∈(data.C j.val).support.toFinset:=by
      rw [←cycle_tail_support_eq G (data.C j.val) (data.hcycle j.val j.property)]
      exact hz
    have hsub:=deleted_path_support_subset_parent G data.s₁ data.s₂ data.u data.v data.P data.c data.d data.hlen data.T
      (fun i _=>data.hT i) (.inl i)
    exact Finset.disjoint_left.mp (data.hcross i.val (Finset.mem_union_left _ i.property) j.val j.property) (hsub hifull) hj
  | inr r =>
    have hdis:=deleted_path_family_vertex_disjoint G data.s₁ data.s₂ data.hs data.u data.v data.P data.hp data.hP data.c data.d
      (lt_of_lt_of_le (by decide : 0<3) data.hc) data.hlen data.T (fun i _=>data.hT i) (.inr r) (.inl i) (by simp)
    exact Finset.disjoint_left.mp hdis hz hifull
end Oberwolfach
