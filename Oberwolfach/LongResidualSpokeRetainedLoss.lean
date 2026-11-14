module

public import Oberwolfach.LongResidualSpokeLocalLoss

@[expose] public section
/-! Only completion vertices that were retained ordinary spokes can
contribute to one-sided loss; newly covered nonspokes do not contribute. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance residualSpokeRetainedLossFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_spoke_retained_loss
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R C:U→Finset (Fin n)) (A:Finset (Fin n)):
    let σ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d σ false t J false false
    let Hold:=fun w=>Finset.univ.filter (fun v=>H false v w);
    (∀w v,v∈rawReservedSpokeList π d σ w→v∉C w→v∈R w\Y w)→
    ∀w,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤
      ((A.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)+
        (((A∩C w)∩Hold w).card:ℝ) :=by
  intro σ Y H Hold hprotect w
  have hsub:A.filter (fun v=>H false v w∧v∉R w\Y w)⊆
      (A.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w)))∪((A∩C w)∩Hold w):=by
    intro v hv
    have ⟨hA,hHold,hnot⟩:=Finset.mem_filter.mp hv
    by_cases hc:v∈C w
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hA,hc⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hHold⟩⟩
    · apply Finset.mem_union_left
      refine Finset.mem_filter.mpr ⟨hA,?_⟩
      intro he
      have hl:v∈rawReservedSpokeList π d σ w:=by
        have hs:=he.mp hHold
        simpa only [rawMarkedPairSpokes,rawMarkedSpokes,rawReservedSpokeList,rawIntervalOrdinaryOuter,
          Finset.mem_filter,Finset.mem_univ,true_and] using hs
      exact hnot (hprotect w v hl hc)
  have hh:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact_mod_cast hh
end Oberwolfach
