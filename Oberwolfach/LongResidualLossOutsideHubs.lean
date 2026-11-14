module

public import Oberwolfach.LongRetentionMismatchLocal

@[expose] public section
/-! Only outer hubs need a completion-image bound: inner hubs are handled by
the exact spoke agreement from the retained correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance residualLossOutsideHubsFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_loss_outside_hubs
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (A:Finset (Fin n)) (inner:Finset U) (R C:U→Finset (Fin n)) (ζ B:ℝ)
    (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t A Finset.univ ζ J)
    (hC:∀w∉inner,((A∩C w).card:ℝ)≤B):
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false;
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→v∈R w\Y w)→
    ∀w∉inner,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤ζ*A.card+B :=by
  intro Y H hprotect w hw
  have hh:=long_residual_spoke_local_loss π d raw t J R C A hprotect w
  have hm:=long_retention_mismatch_local π d raw t J A ζ hrows w
  exact hh.trans (add_le_add hm (hC w hw))
end Oberwolfach
