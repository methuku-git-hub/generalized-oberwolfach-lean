module

public import Oberwolfach.RetentionRestrictionCommonEvent
public import Oberwolfach.RetainedMarkedRootUniformity

@[expose] public section
/-! If the retained colour has no raw starts, retaining it changes nothing
and all its retained root types are empty. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retention_good_and_empty_roots_of_no_starts
    {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (hzero:∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x g)
    (S:I→Finset V) (T:I→Finset U) (ζ:ℝ) (hζ:0≤ζ):
    RetainedRestrictionGood π d σ g t S T ζ J ∧
    (∀w,IsEmpty (retainedMarkedIndex π d σ g t J w)):=by
  have heq:∀x w,retainedRawFamilyState π d σ g t J (x,w)=rawIntervalFamilyState π d σ (x,w):=by
    intro x w
    by_contra hne
    have hchange:retainedIntervalState π d (fun e=>σ (w,e)) (retainedRawStart π d σ g t J w) x≠
        rawIntervalState π d (fun e=>σ (w,e)) x:=by
      simpa only [retainedRawFamilyState,rawIntervalFamilyState] using hne
    obtain ⟨a,ha,_,_⟩:=retainedIntervalState_change_selected π d (fun e=>σ (w,e))
      (retainedRawStart π d σ g t J w) (fun _ _ h=>h.1) g
      (fun a g' hg h=>⟨h,fun hh=>False.elim (hg hh)⟩) x hchange
    exact hzero w a ha
  constructor
  · intro i
    constructor
    · intro w
      simp only [heq,ne_eq,not_true_eq_false,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
      positivity
    · intro x
      simp only [heq,ne_eq,not_true_eq_false,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
      positivity
  · intro w
    refine ⟨?_⟩
    intro x
    exact hzero w x.val x.property.1
end Oberwolfach
