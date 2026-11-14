module

public import Oberwolfach.OrdinaryForcedTargetsAvoidReserved

@[expose] public section
/-! Targets in the protected pair cost at most the two inner-set sizes, and
    covering them while avoiding reference spokes yields exact agreement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryInnerSpokeTargets (Inner:Finset V) (Hubs:Finset U) (Reference:V→U→Prop) (u:U):Finset V :=
  if u∈Hubs then Inner.filter (fun v=>¬Reference v u) else ∅

theorem ordinary_inner_spoke_targets_bounds
    (Inner:Finset V) (Hubs:Finset U) (Reference:V→U→Prop):
    (∀u,(ordinaryInnerSpokeTargets Inner Hubs Reference u).card≤Inner.card) ∧
    (∀v,(Finset.univ.filter (fun u=>v∈ordinaryInnerSpokeTargets Inner Hubs Reference u)).card≤Hubs.card) ∧
    (∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Reference u→¬Reference v u):=by
  constructor
  · intro u
    by_cases hu:u∈Hubs
    · simp only [ordinaryInnerSpokeTargets,hu,ite_true]
      exact Finset.card_filter_le _ _
    · simp [ordinaryInnerSpokeTargets,hu]
  constructor
  · intro v
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
    by_contra hn
    simp [ordinaryInnerSpokeTargets,hn] at hu
  · intro u v hv
    by_cases hu:u∈Hubs
    · have hh:v∈Inner ∧ ¬Reference v u:=by
        simpa only [ordinaryInnerSpokeTargets,hu,ite_true,Finset.mem_filter] using hv
      exact hh.2
    · simp [ordinaryInnerSpokeTargets,hu] at hv

theorem ordinary_inner_spokes_exact_from_forced_targets
    (Inner:Finset V) (Hubs:Finset U) (Reference:V→U→Prop) (Image:U→Finset V)
    (hAvoid:∀u v,v∈Image u→¬Reference v u)
    (hCover:∀u,ordinaryInnerSpokeTargets Inner Hubs Reference u⊆Image u):
    ∀v∈Inner,∀u∈Hubs,(v∉Image u ↔ Reference v u):=by
  intro v hv u hu
  constructor
  · intro hnot
    by_contra hn
    have hvT:v∈ordinaryInnerSpokeTargets Inner Hubs Reference u:=by
      simp [ordinaryInnerSpokeTargets,hu,hv,hn]
    exact hnot (hCover u hvT)
  · intro hr hi
    exact hAvoid u v hi hr
end Oberwolfach
