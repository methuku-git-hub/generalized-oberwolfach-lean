module

public import Oberwolfach.RawReservedSpokeList
public import Oberwolfach.InnerRequiredRawStateCover

@[expose] public section
/-! Retention only removes interval starts. A reserved raw ordinary label
therefore remains ordinary and cannot become a retained marked label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_reserved_spoke_list_disjoint_retained_marked
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U):
    Disjoint (rawReservedSpokeList π d σ w) (retainedFinalMarkedAt π d σ t J w):=by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hraw:rawIntervalState π d (fun e=>σ (w,e)) x=some (Sum.inr false):=by
    simpa only [rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,
      true_and,rawIntervalFamilyState] using hx
  have hblock:¬rawIntervalBlocked π d (fun e=>σ (w,e)) x:=by
    intro hb
    unfold rawIntervalState at hraw
    split_ifs at hraw <;> simp_all
  have heq:=retainedIntervalState_eq_of_no_deletion π d (fun e=>σ (w,e))
    (retainedRawStart π d σ false t J w) (fun _ _ h=>h.1) x
    (by intro a g ha hax;exact False.elim (hblock ⟨g,a,ha,hax⟩))
  have hret:retainedIntervalState π d (fun e=>σ (w,e)) (retainedRawStart π d σ false t J w) x=
      some (Sum.inl false):=by
    simpa only [retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and,retainedRawFamilyState] using hy
  rw [hraw] at heq
  rw [hret] at heq
  cases heq
end Oberwolfach
