module

public import Oberwolfach.LongResidualLossOutsideHubs
public import Oberwolfach.CompletionProtectedImageMatchingBound

@[expose] public section
/-! The protected completion supplies the outer-hub loss bound using its
own prescribed vertices and assigned matching edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance outerProtectedCompletionLossFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_loss_from_outer_protected_completion
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (A:Finset (Fin n)) (inner:Finset U) (R:U→Finset (Fin n)) (ζ P L:ℝ)
    (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t A Finset.univ ζ J)
    (X:U→Type) [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (B:∀w,Finset (X w)) (Φ g:∀w,X w→Fin n)
    (Lists Pre Required:U→Finset (Fin n)) (M:U→Finset (Fin n×Fin n))
    (hfixed:∀w x,x∈B w→Φ w x=g w x)
    (hfree:∀w x,x∉B w→Φ w x∈Lists w)
    (havoid:∀w,Disjoint (Lists w) A)
    (hforced:∀w,(B w).image (g w)=Pre w∪prescribedMatchingEndpoints (M w)∪Required w)
    (hPre:∀w∉inner,((Pre w).card:ℝ)≤P) (hM:∀w∉inner,((M w).card:ℝ)≤L)
    (hRequired:∀w∉inner,Required w=∅):
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false;
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉Finset.univ.image (Φ w)→v∈R w\Y w)→
    ∀w∉inner,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤ζ*A.card+(P+2*L) :=by
  intro Y H hprotect
  have hC:∀w∉inner,((A∩Finset.univ.image (Φ w)).card:ℝ)≤P+2*L:=by
    intro w hw
    have hh:=completion_protected_image_matching_bound A (B w) (Φ w) (g w) (Lists w)
      (Pre w) (Required w) (M w) (hfixed w) (hfree w) (havoid w) (hforced w)
    have hh':((A∩Finset.univ.image (Φ w)).card:ℝ)≤
        ((Pre w).card:ℝ)+2*((M w).card:ℝ)+(Required w).card:=by
      have hcast:(((Finset.univ.image (Φ w))∩A).card:ℝ)≤
          ((Pre w).card:ℝ)+2*((M w).card:ℝ)+(Required w).card:=by exact_mod_cast hh
      simpa only [Finset.inter_comm] using hcast
    rw [hRequired w hw] at hh'
    simp only [Finset.card_empty,Nat.cast_zero,add_zero] at hh'
    linarith [hPre w hw,hM w hw]
  exact long_residual_loss_outside_hubs π d raw t J A inner R (fun w=>Finset.univ.image (Φ w)) ζ (P+2*L) hrows hC hprotect
end Oberwolfach
