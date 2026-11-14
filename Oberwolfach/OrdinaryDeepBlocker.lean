module

public import Oberwolfach.PhysicalHostDegreeBounds
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! A bounded-degree physical blocker for a still-deeper ordinary pair.
The rim blocker contains all potential edges inside the deeper rim set; the
spoke blocker contains all potential incidences of the two deeper sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryDeepRimBlocker (T:Finset V):SimpleGraph V := spanningRestriction ⊤ T

def ordinaryDeepSpokeBlocker (T:Finset V) (W:Finset U):V→U→Prop := fun v u=>v∈T ∧ u∈W

def ordinaryDeepBlocker (T:Finset V) (W:Finset U):SimpleGraph (V⊕U) :=
  ordinaryPhysicalGraph (ordinaryDeepRimBlocker T) (ordinaryDeepSpokeBlocker T W)

theorem ordinary_deep_rim_blocker_adj (T:Finset V) (v w:V):
    (ordinaryDeepRimBlocker T).Adj v w ↔ v≠w ∧ v∈T ∧ w∈T := by
  rw [ordinaryDeepRimBlocker,spanningRestriction_adj]
  simp

theorem ordinary_deep_rim_blocker_degree (T:Finset V) (v:V):
    (ordinaryDeepRimBlocker T).degree v ≤ T.card := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw
  exact ((ordinary_deep_rim_blocker_adj T v w).mp hw).2.2

theorem ordinary_deep_blocker_degree (T:Finset V) (W:Finset U) (z:V⊕U):
    ((ordinaryDeepBlocker T W).degree z:ℝ) ≤ (T.card:ℝ)+(W.card:ℝ) := by
  apply ordinary_physical_degree_bound (ordinaryDeepRimBlocker T) (ordinaryDeepSpokeBlocker T W)
    T.card W.card T.card ((T.card:ℝ)+(W.card:ℝ))
  · intro v; exact_mod_cast ordinary_deep_rim_blocker_degree T v
  · intro v
    have h:(Finset.univ.filter (ordinaryDeepSpokeBlocker T W v))⊆W := by
      intro u hu
      exact (Finset.mem_filter.mp hu).2.2
    exact_mod_cast Finset.card_le_card h
  · intro u
    have h:(Finset.univ.filter (fun v=>ordinaryDeepSpokeBlocker T W v u))⊆T := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2.1
    exact_mod_cast Finset.card_le_card h
  · rfl
  · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
end Oberwolfach
