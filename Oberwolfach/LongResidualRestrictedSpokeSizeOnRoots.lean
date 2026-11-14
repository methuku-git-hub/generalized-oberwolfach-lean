module

public import Oberwolfach.LongRetentionMismatchFromGlobalEvent
public import Oberwolfach.LongResidualSpokeCompletionControl
public import Oberwolfach.MarkedSpokeChangesFromLoss

@[expose] public section
/-! An alternative to bounding new residual spokes directly: a local bound
on the net spoke-count change combines with one-sided completion loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance restrictedSpokeSizeOnRootsFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_restricted_spoke_change_from_size_on_roots
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (B:Finset U) (Roots:Finset (Fin n)) (R C:U→Finset (Fin n)) (ζ load size:ℝ)
    (hζ:0≤ζ) (hU:Fintype.card U≤n)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J):
    let Y:=fun w=>markedIntervalRootSet π
      (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false;
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→v∈R w\Y w)→
    (∀v∈Roots,((B.filter (fun w=>v∈C w)).card:ℝ)≤load)→
    (∀v∈Roots,((B.filter (fun w=>v∈R w\Y w)).card:ℝ)-((B.filter (fun w=>H false v w)).card:ℝ)≤size)→
    ∀v∈Roots,(∑w∈B,if ¬(H false v w↔v∈R w\Y w) then (1:ℝ) else 0)≤2*(ζ*n+load)+size :=by
  intro Y H hprotect hload hsize v hv
  have hmismatch:=(long_retention_mismatch_from_global_event π d raw false false false t J ζ hζ (by simpa using hU) hgood).1 false v
  let Old:=B.filter (fun w=>H false v w)
  let New:=B.filter (fun w=>v∈R w\Y w)
  have hsub:Old\New ⊆
      (Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))) ∪
      (B.filter (fun w=>v∈C w)):=by
    intro w hw
    have ⟨hwold,hwnew⟩:=Finset.mem_sdiff.mp hw
    have ⟨hwB,hH⟩:=Finset.mem_filter.mp hwold
    have hnot:v∉R w\Y w:=by
      intro hmem
      exact hwnew (Finset.mem_filter.mpr ⟨hwB,hmem⟩)
    by_cases he:H false v w↔rawMarkedPairSpokes π d raw false false false v w
    · have hl:v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w:=by
        have hs:=he.mp hH
        simpa only [rawMarkedPairSpokes,rawMarkedSpokes,rawReservedSpokeList,rawIntervalOrdinaryOuter,
          Finset.mem_filter,Finset.mem_univ,true_and] using hs
      have hc:v∈C w:=by
        by_contra hc
        exact hnot (hprotect w v hl hc)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwB,hc⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have hloss:((Old\New).card:ℝ)≤ζ*n+load:=by
    have hn:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hn':((Old\New).card:ℝ)≤
      ((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)+
      ((B.filter (fun w=>v∈C w)).card:ℝ):=by exact_mod_cast hn
    simp only [Fintype.card_fin] at hmismatch
    linarith [hload v hv]
  have hchange:B.filter (fun w=>¬(H false v w↔v∈R w\Y w))=changed Old New:=by
    ext w
    simp only [Finset.mem_filter,changed,Finset.mem_union,Finset.mem_sdiff,Old,New]
    tauto
  have hsum:(∑w∈B,if ¬(H false v w↔v∈R w\Y w) then (1:ℝ) else 0)=((changed Old New).card:ℝ):=by
    rw [←hchange]
    simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hsum,changed_card_from_loss_and_size]
  have hs:=hsize v hv
  change (New.card:ℝ)-(Old.card:ℝ)≤size at hs
  linarith
end Oberwolfach
