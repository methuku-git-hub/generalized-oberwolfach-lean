module

public import Oberwolfach.RetentionNoStartsGood
public import Oberwolfach.UniformStartRetentionMinimum

@[expose] public section
/-! If a sampled marked colour has no starts, its canonical retention size
and every feasible retained set are exactly zero. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retention_is_zero_of_no_starts
    {V U Γ Color:Type} [Fintype V] [Nonempty V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ)
    (hzero:∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x g):
    (∀x,rawStartHubSet π d σ g x=∅) ∧
    startRetentionMinimum (rawStartHubSet π d σ g)=0 ∧
    ∀t (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
      t=0 ∧ ∀x,startRetainedHubs (rawStartHubSet π d σ g) t J x=∅:=by
  have hHub:∀x,rawStartHubSet π d σ g x=∅:=by
    intro x
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hzero w x (Finset.mem_filter.mp hw).2
  have hmin:startRetentionMinimum (rawStartHubSet π d σ g)=0:=by
    have hh:=startRetentionMinimum_le (rawStartHubSet π d σ g) (Classical.choice inferInstance)
    rw [hHub,Finset.card_empty] at hh
    omega
  refine ⟨hHub,hmin,?_⟩
  intro t J
  have hRet:∀x,startRetainedHubs (rawStartHubSet π d σ g) t J x=∅:=by
    intro x
    have hh:=startRetainedHubs_subset (rawStartHubSet π d σ g) t J x
    rw [hHub] at hh
    exact Finset.subset_empty.mp hh
  have ht:=startRetainedHubs_card (rawStartHubSet π d σ g) t J (Classical.choice inferInstance)
  rw [hRet,Finset.card_empty] at ht
  exact ⟨ht.symm,hRet⟩
end Oberwolfach
