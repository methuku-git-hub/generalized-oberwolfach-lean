module

public import Oberwolfach.GenericRetainedMatchingLabels

@[expose] public section
/-! A raw reserved ordinary spoke cannot become a retained marked spoke:
retained marked intervals are contained in the originally covered intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_spoke_avoids_retained_marked
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U):
    Disjoint (rawReservedSpokeList π d σ w) (retainedFinalMarkedAt π d σ t J w):=by
  apply Finset.disjoint_left.mpr
  intro v hreserved hmarked
  have hstate:retainedRawFamilyState π d σ false t J (v,w)=some (Sum.inl false):=by
    simpa [retainedFinalMarkedAt] using hmarked
  have hR:∀a g,retainedRawStart π d σ false t J w a g→ rawIntervalColouredStart π d (fun e=>σ (w,e)) a g:=fun _ _ h=>h.1
  have hret:retainedIntervalState π d (fun e=>σ (w,e)) (retainedRawStart π d σ false t J w) v=some (Sum.inl false):=hstate
  obtain ⟨a,ha,hwin⟩:=(retainedIntervalState_interval_iff π d (fun e=>σ (w,e)) _ hR v false).mp hret
  have hcovered:∃g,rawIntervalCovered π d (fun e=>σ (w,e)) v g:=⟨false,a,ha.1,hwin⟩
  have hraw:rawIntervalFamilyState π d σ (v,w)=some (Sum.inr false):=by
    simpa [rawReservedSpokeList,rawIntervalOrdinaryOuter] using hreserved
  simp [rawIntervalFamilyState,rawIntervalState,hcovered] at hraw
end Oberwolfach
