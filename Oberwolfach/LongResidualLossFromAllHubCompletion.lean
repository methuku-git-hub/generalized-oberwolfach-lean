module

public import Oberwolfach.LongResidualSpokeRetainedLoss
public import Oberwolfach.LongRetentionMismatchLocal
public import Oberwolfach.CompletionProtectedRetainedImageBound

@[expose] public section
/-! Covering missing targets at every hub leaves only prescribed and
assigned endpoints as possible retained-spoke losses on the vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance allHubCompletionLossFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_loss_from_all_hub_completion
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (A:Finset (Fin n)) (R:U→Finset (Fin n)) (ζ P L:ℝ)
    (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t A Finset.univ ζ J)
    (X:U→Type) [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (B:∀w,Finset (X w)) (Φ g:∀w,X w→Fin n)
    (Lists Pre Required:U→Finset (Fin n)) (M:U→Finset (Fin n×Fin n))
    (hfixed:∀w x,x∈B w→Φ w x=g w x)
    (hfree:∀w x,x∉B w→Φ w x∈Lists w)
    (havoid:∀w,Disjoint (Lists w) A)
    (hforced:∀w,(B w).image (g w)=Pre w∪prescribedMatchingEndpoints (M w)∪Required w)
    (hPre:∀w,((Pre w).card:ℝ)≤P) (hM:∀w,((M w).card:ℝ)≤L):
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false
    let Hold:=fun w=>Finset.univ.filter (fun v=>H false v w);
    (∀w,Disjoint (Required w) (Hold w))→
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉Finset.univ.image (Φ w)→v∈R w\Y w)→
    ∀w,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤ζ*A.card+P+2*L :=by
  intro Y H Hold hRequired hprotect w
  have hC:=completion_protected_retained_image_bound A (Hold w) (B w) (Φ w) (g w) (Lists w)
    (Pre w) (Required w) (M w) (hfixed w) (hfree w) (havoid w) (hRequired w) (hforced w)
  have hC':(((A∩Finset.univ.image (Φ w))∩Hold w).card:ℝ)≤P+2*L:=by
    have hcast:((((Finset.univ.image (Φ w))∩A)∩Hold w).card:ℝ)≤
        ((Pre w).card:ℝ)+2*((M w).card:ℝ):=by exact_mod_cast hC
    have hcast':(((A∩Finset.univ.image (Φ w))∩Hold w).card:ℝ)≤
        ((Pre w).card:ℝ)+2*((M w).card:ℝ):=by simpa only [Finset.inter_comm] using hcast
    linarith [hPre w,hM w]
  have hm:=long_retention_mismatch_local π d raw t J A ζ hrows w
  have hh:=long_residual_spoke_retained_loss π d raw t J R (fun w=>Finset.univ.image (Φ w)) A hprotect w
  linarith
end Oberwolfach
