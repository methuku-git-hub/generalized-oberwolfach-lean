module

public import Oberwolfach.ActualSelectedRunProperties
public import Oberwolfach.CycleWalkTailSupport

@[expose] public section
/-! The selected cycles (with the first edge removed) and selected runs form
one family of pairwise disjoint actual source paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
  {G:SimpleGraph X}

def actualOldPieceIndex (data:ActualResidualData (K:=K) (J:=J) G):Type:=
  {j // j∈data.t} ⊕ SelectedRunIndex data.s₂ data.d data.T

instance (data:ActualResidualData (K:=K) (J:=J) G):Fintype (actualOldPieceIndex data):=by
  unfold actualOldPieceIndex
  infer_instance

def actualOldPieceStart (data:ActualResidualData (K:=K) (J:=J) G):actualOldPieceIndex data→X
  | .inl j=>(data.C j.val).snd
  | .inr r=>data.start (.inr r)

def actualOldPieceFinish (data:ActualResidualData (K:=K) (J:=J) G):actualOldPieceIndex data→X
  | .inl j=>data.root j.val
  | .inr r=>data.finish (.inr r)

def actualOldPieceWalk (data:ActualResidualData (K:=K) (J:=J) G):
    ∀z:actualOldPieceIndex data,G.Walk (actualOldPieceStart data z) (actualOldPieceFinish data z)
  | .inl j=>(data.C j.val).tail
  | .inr r=>data.path (.inr r)

theorem actual_old_piece_walks_are_disjoint_simple_paths
    (data:ActualResidualData (K:=K) (J:=J) G):
    (∀z,(actualOldPieceWalk data z).IsPath) ∧
    (∀z w,z≠w→Disjoint (actualOldPieceWalk data z).support.toFinset (actualOldPieceWalk data w).support.toFinset):=by
  classical
  have hr:=actual_selected_runs_are_disjoint_simple_paths data
  have hcross:∀(j:{j // j∈data.t}) (r:SelectedRunIndex data.s₂ data.d data.T),
      Disjoint (data.C j.val).tail.support.toFinset (data.path (.inr r)).support.toFinset:=by
    intro j r
    rw [cycle_tail_support_eq G (data.C j.val) (data.hcycle j.val j.property)]
    have hsub:=deleted_path_support_subset_parent G data.s₁ data.s₂ data.u data.v data.P data.c data.d data.hlen data.T
      (fun i _=>data.hT i) (.inr r)
    have hdis:=data.hcross r.1.val (Finset.mem_union_right _ r.1.property) j.val j.property
    exact hdis.symm.mono_right hsub
  constructor
  · intro z
    cases z with
    | inl j =>exact (data.hcycle j.val j.property).isPath_tail
    | inr r =>exact hr.1 r
  · intro z w hne
    cases z with
    | inl i =>
      cases w with
      | inl j =>
        rw [show (actualOldPieceWalk data (.inl i)).support.toFinset=(data.C i.val).support.toFinset from cycle_tail_support_eq G _ (data.hcycle i.val i.property)]
        rw [show (actualOldPieceWalk data (.inl j)).support.toFinset=(data.C j.val).support.toFinset from cycle_tail_support_eq G _ (data.hcycle j.val j.property)]
        exact data.hC i.property j.property (fun h=>hne (congrArg (fun z:{j // j∈data.t}=>(Sum.inl z:actualOldPieceIndex data)) (Subtype.ext h)))
      | inr r =>exact hcross i r
    | inr r =>
      cases w with
      | inl j =>exact (hcross j r).symm
      | inr s =>exact hr.2 r s (fun h=>hne (by subst s; rfl))
end Oberwolfach
