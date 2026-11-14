module

public import Oberwolfach.LongResidualReservedSpokeLossByAgreement

@[expose] public section
/-! Restrict the one-sided spoke loss to an arbitrary vertex set. The only
completion contribution is the image inside that set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance residualSpokeLocalLossFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_spoke_local_loss
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R C:U→Finset (Fin n)) (A:Finset (Fin n)):
    let σ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d σ false t J false false;
    (∀w v,v∈rawReservedSpokeList π d σ w→v∉C w→v∈R w\Y w)→
    ∀w,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤
      ((A.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)+(A∩C w).card :=by
  intro σ Y H hprotect w
  have hpoint:∀v,H false v w→v∉R w\Y w→
      ¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w)∨v∈C w:=by
    intro v hHold hnot
    by_cases hc:v∈C w
    · exact Or.inr hc
    · left
      intro he
      have hl:v∈rawReservedSpokeList π d σ w:=by
        have hs:=he.mp hHold
        simpa only [rawMarkedPairSpokes,rawMarkedSpokes,rawReservedSpokeList,rawIntervalOrdinaryOuter,
          Finset.mem_filter,Finset.mem_univ,true_and] using hs
      exact hnot (hprotect w v hl hc)
  have hsub:A.filter (fun v=>H false v w∧v∉R w\Y w)⊆
      (A.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w)))∪(A∩C w):=by
    intro v hv
    simp only [Finset.mem_filter,Finset.mem_inter,Finset.mem_union] at hv ⊢
    rcases hpoint v hv.2.1 hv.2.2 with hh|hh
    · exact Or.inl ⟨hv.1,hh⟩
    · exact Or.inr ⟨hv.1,hh⟩
  have hh:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact_mod_cast hh
end Oberwolfach
