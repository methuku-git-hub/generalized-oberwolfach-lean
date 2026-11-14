module

public import Oberwolfach.MarkedReservedRimPairCount
public import Oberwolfach.Neighbourhoods
public import Oberwolfach.RandomColourCuts

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance candidateIncomingDecEq : DecidableEq V := Classical.decEq V
local instance candidateIncomingArcDecEq (P:V×V→Prop) : DecidableEq {e:V×V // P e} := Classical.decEq _

def markedRawIncomingTails (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (v:V):Finset V:=
  Finset.univ.filter (fun x=>sampledColourOrientation G ω 1 x v=1)

def markedCandidateIncomingTails (P:V×V→Prop) (M:Finset {e:V×V // P e}) (v:V):Finset V:=
  (M.filter (fun e=>e.val.2=v)).image (fun e=>e.val.1)

theorem marked_raw_incoming_tails_card (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (v:V):
    (markedRawIncomingTails G ω v).card=∑x,sampledColourOrientation G ω 1 x v :=by
  unfold markedRawIncomingTails
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x hx
  unfold sampledColourOrientation
  split_ifs <;> simp_all

theorem marked_candidate_incoming_tails_card (P:V×V→Prop)
    (M:Finset {e:V×V // P e}) (v:V):
    (markedCandidateIncomingTails P M v).card=directedInCount P M v :=by
  unfold markedCandidateIncomingTails directedInCount
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  apply Subtype.ext
  apply Prod.ext hab
  exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm

/-- The raw selected incoming count transfers to the residual candidate set
with only the explicitly measured change in its incoming tails. -/
theorem marked_candidate_indegree_deviation_from_raw
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (P:V×V→Prop)
    (M:Finset {e:V×V // P e}) (b:ℕ) (err loss:ℝ)
    (hraw:∀v,|((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ)-b|≤err)
    (hchange:∀v,((changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P M v)).card:ℝ)≤loss):
    ∀v,|(directedInCount P M v:ℝ)-b|≤err+loss :=by
  intro v
  have hh:|((markedCandidateIncomingTails P M v).card:ℝ)-(markedRawIncomingTails G ω v).card|≤loss:=by
    have h:=(card_difference_le_changed (markedCandidateIncomingTails P M v) (markedRawIncomingTails G ω v))
    have heq:changed (markedCandidateIncomingTails P M v) (markedRawIncomingTails G ω v)=
      changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P M v):=by
      ext x;simp [changed,or_comm]
    rw [heq] at h
    exact h.trans (hchange v)
  rw [marked_candidate_incoming_tails_card,marked_raw_incoming_tails_card] at hh
  have hr:=hraw v
  have htriangle:=abs_add_le ( (directedInCount P M v:ℝ)-((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ))
    (((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ)-(b:ℝ))
  have hid:((directedInCount P M v:ℝ)-((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ))+
    (((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ)-(b:ℝ))=(directedInCount P M v:ℝ)-b:=by ring
  rw [hid] at htriangle
  linarith only [htriangle,hh,hr]
end Oberwolfach
