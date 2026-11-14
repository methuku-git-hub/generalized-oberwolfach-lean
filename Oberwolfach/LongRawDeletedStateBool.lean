module

public import Oberwolfach.LongRawSurvivingStateIdentity

@[expose] public section
/-! The deletion-filtered resource indicator is the Boolean state of the
same raw outcome with its physical rim edges deleted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_surviving_bool_state
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    (fun z=>decide (z∈longRawSurvivingResources P π d raw g j F)) =
      longRawHubState P π d (rawMarkedDeleteRims raw F) g j :=by
  funext z
  rw [long_raw_surviving_state_is_raw_rim_deletion]
  simp only [mem_bernoulliVertexSet,decide_eq_true_eq]
  cases h:longRawHubState P π d (rawMarkedDeleteRims raw F) g j z <;> simp [h]
end Oberwolfach
