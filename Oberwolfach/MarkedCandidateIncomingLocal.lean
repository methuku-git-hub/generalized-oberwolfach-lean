module

public import Oberwolfach.MarkedCandidateIncomingPerturbation

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance candidateIncomingLocalDecEq : DecidableEq V := Classical.decEq V
local instance candidateIncomingLocalArcDecEq (P:V×V→Prop) : DecidableEq {e:V×V // P e} := Classical.decEq _

theorem marked_candidate_indegree_deviation_from_raw_local
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (P:V×V→Prop)
    (M:Finset {e:V×V // P e}) (b:ℕ) (err loss:ℝ) (I:Finset V)
    (hraw:∀v,|((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ)-b|≤err)
    (hchange:∀v,v∉I→((changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P M v)).card:ℝ)≤loss):
    ∀v,v∉I→|(directedInCount P M v:ℝ)-b|≤err+loss :=by
  intro v hv
  have hh:|((markedCandidateIncomingTails P M v).card:ℝ)-(markedRawIncomingTails G ω v).card|≤loss:=by
    have h:=(card_difference_le_changed (markedCandidateIncomingTails P M v) (markedRawIncomingTails G ω v))
    have heq:changed (markedCandidateIncomingTails P M v) (markedRawIncomingTails G ω v)=
      changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P M v):=by
      ext x;simp [changed,or_comm]
    rw [heq] at h
    exact h.trans (hchange v hv)
  rw [marked_candidate_incoming_tails_card,marked_raw_incoming_tails_card] at hh
  have hr:=hraw v
  have htriangle:=abs_add_le ( (directedInCount P M v:ℝ)-((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ))
    (((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ)-(b:ℝ))
  have hid:((directedInCount P M v:ℝ)-((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ))+
    (((∑x,sampledColourOrientation G ω 1 x v:ℕ):ℝ)-(b:ℝ))=(directedInCount P M v:ℝ)-b:=by ring
  rw [hid] at htriangle
  linarith only [htriangle,hh,hr]
end Oberwolfach
