module

public import Oberwolfach.InnerRequiredRawStateCover
public import Oberwolfach.RawIntervalExtendedHubsUpper
public import Oberwolfach.RetainedIntervalIdentities

@[expose] public section
/-! The retained absorber labels are counted by the common extended-hub test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_marked_absorber_occurrence_on_le_extended
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (H:Finset U) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t):
    ∀v,(H.filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card≤
      (rawIntervalExtendedAnyHubSet π d σ v ∩ H).card:=by
  intro v
  apply Finset.card_le_card
  intro w hw
  have hwH:w∈H:=(Finset.mem_filter.mp hw).1
  apply Finset.mem_inter.mpr
  refine ⟨?_,hwH⟩
  have hstate:retainedRawFamilyState π d σ false t J (v,w)=some (Sum.inl false):=by
    simpa only [retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using (Finset.mem_filter.mp hw).2
  have hR:∀a g,retainedRawStart π d σ false t J w a g→ rawIntervalColouredStart π d (fun e=>σ (w,e)) a g:=fun _ _ h=>h.1
  have hret:retainedIntervalState π d (fun e=>σ (w,e)) (retainedRawStart π d σ false t J w) v=some (Sum.inl false):=hstate
  obtain ⟨a,ha,hwin⟩:=(retainedIntervalState_interval_iff π d (fun e=>σ (w,e)) _ hR v false).mp hret
  have hwin':v∈permutationWindow π 0 d a:=permutationWindow_mono π (le_refl 0) (Nat.sub_le d 1) a hwin
  apply Finset.mem_union_left
  simp only [rawIntervalExtendedHubSet,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨a,ha.1,hwin'⟩
end Oberwolfach
