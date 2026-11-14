module

public import Oberwolfach.OrdinaryZeroRetentionPrior

@[expose] public section
/-! The empty retained outcome is available deterministically; no second
sampling choice is needed to apply a deletion-uniform matching event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryEmptyRetentionOutcome {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] (A:V→Finset U):StartRetentionOutcome A 0 :=
  fun _=>⟨∅,by simp⟩

theorem ordinary_zero_retention_event_empty_outcome
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (g:Γ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (h:OrdinaryZeroRetentionEvent π d g σ) (ζ:ℝ) (hζ:0≤ζ):
    let σI:=fun e=>σ (Sum.inr e)
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d σI g);
    RetainedRestrictionGood π d σI g 0 (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J ∧
      (∀w,IsEmpty (retainedMarkedIndex π d σI g 0 J w)) :=by
  intro σI J
  exact h.2 0 J ζ hζ
end Oberwolfach
