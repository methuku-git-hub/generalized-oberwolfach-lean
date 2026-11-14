module

public import Oberwolfach.OccurrenceIncidentWeights

@[expose] public section
/-! Bound the realised pair-weight cost using the two endpoint degrees of
an arbitrary deletion set. No sampling density enters this bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A V:Type} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

theorem adaptive_deleted_pair_sum_bound
    (Deleted:Finset A) (tail head:A→V) (d M N:ℝ) (hM:0≤M) (hN:0≤N)
    (hout:∀x,(∑a,if a∈Deleted ∧ tail a=x then (1:ℝ) else 0)≤d)
    (hin:∀x,(∑a,if a∈Deleted ∧ head a=x then (1:ℝ) else 0)≤d)
    (S T:Finset V) (pair:A→ℝ)
    (hpair:∀a∈Deleted,pair a≤(if tail a∈S ∨ head a∈T then M else N)):
    (∑a∈Deleted,pair a)≤d*((S.card+T.card:ℝ)*M+(Fintype.card V:ℝ)*N) :=by
  have hi:=occurrence_root_incident_cost tail head (·∈Deleted) d (by
    intro x
    convert hout x using 1
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl) (by
    intro x
    convert hin x using 1
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl) S T M N hM hN
  have hb:(∑a∈Deleted,pair a)≤∑a∈Deleted,(if tail a∈S ∨ head a∈T then M else N):=
    Finset.sum_le_sum hpair
  have he:(∑a∈Deleted,(if tail a∈S ∨ head a∈T then M else N))=
      ∑a,if a∈Deleted then (if tail a∈S ∨ head a∈T then M else N) else 0:=by
    simp only [Finset.sum_ite_mem,Finset.univ_inter]
  apply hb.trans
  rw [he]
  convert hi using 1
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> rfl
end Oberwolfach
