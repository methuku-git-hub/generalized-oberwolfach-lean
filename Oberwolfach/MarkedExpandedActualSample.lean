module

public import Oberwolfach.MixedClassActualRetention

@[expose] public section
/-! The retained marked sample, as a deterministic projection of the
expanded mixed outcome and its retention witness. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

abbrev MarkedExpandedActualOutcome (π:Equiv.Perm V) (d:ℕ):Type :=
  Σ ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e,
    StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false))

def markedExpandedActualSelected (π:Equiv.Perm V) (d:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d):RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false :=
  ⟨(fun e=>rawExpandedMarkedCollapse e (z.1 e)),z.2⟩

/-- The common-event law uses exactly this expanded outcome space. -/
theorem marked_expanded_actual_outcome_eq_mixed (π:Equiv.Perm V) (d:ℕ):
    MarkedExpandedActualOutcome (U:=U) π d =
      (Σ ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e,
        mixedClassRetentionSpace true π d false ω) := by
  rfl

/-- Its retained projection is the collapse used by the matching theorem. -/
theorem marked_expanded_actual_selected_eq (π:Equiv.Perm V) (d:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d):
    markedExpandedActualSelected π d z=⟨(fun e=>rawExpandedMarkedCollapse e (z.1 e)),z.2⟩ := by
  rfl
end Oberwolfach
