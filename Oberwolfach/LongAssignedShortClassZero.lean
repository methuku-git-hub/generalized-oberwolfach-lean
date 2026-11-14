module

public import Oberwolfach.LongAssignedSeedTargets

@[expose] public section
/-! A 2-factor has no cycles of length one or two. The corresponding
frequency and its retained contribution therefore vanish identically. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

theorem long_assigned_fraction_below_three_zero
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (i:Fin K) (hi:i.val+1<3) (u:U):
    ordinaryAssignedFraction F hF K u (some i)=0 := by
  have hnone:∀v,longPreparationCycleClass (F u) (hF u) K v≠some i := by
    intro v h
    have hc:3≤Fintype.card ((F u).connectedComponentMk v):=
      (component_regular_two_cycle_iso (F u) (hF u) ((F u).connectedComponentMk v)).1
    have he:=((long_preparation_cycle_class (F u) (hF u) K v).2 i).mp h
    omega
  unfold ordinaryAssignedFraction
  simp [hnone]

theorem long_assigned_kept_below_three_zero
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (i:Fin K) (hi:i.val+1<3) (θ:ℝ) (u:U):
    longAssignedKeptFraction F hF K θ i u=0 ∧
      longAssignedKeptOrdinaryContribution F hF K θ i u=0 := by
  have hh:=long_assigned_fraction_below_three_zero F hF K i hi u
  constructor
  · unfold longAssignedKeptFraction
    simp [hh]
  · rw [long_assigned_kept_fraction_contribution]
    unfold longAssignedKeptFraction
    simp [hh]
end Oberwolfach
