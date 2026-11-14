module

public import Oberwolfach.LongResidualSpokeCompletionControl
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section
/-! For the same residual complement, ordinary spoke losses are bounded by
retention-label changes plus the actual completion-image load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance residualReservedSpokeLossFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_reserved_spoke_loss
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ:ℝ)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ):
    let σ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d σ false t J false false;
    (∀v,((Finset.univ.filter (fun w=>H false v w∧v∉R w\Y w)).card:ℝ)≤
      ((Finset.univ.filter (fun w=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w))).card:ℝ)+
      (δ*n+(Real.sqrt δ*n+1))) ∧
    (∀w,((Finset.univ.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤
      ((Finset.univ.filter (fun v=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w))).card:ℝ)+10*θ*n):=by
  intro σ Y H
  obtain ⟨C,hrow,hcol,hprotect⟩:=hcontrol
  have hpoint:∀v w,H false v w→v∉R w\Y w→
      retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w)∨v∈C w:=by
    intro v w hHold hnot
    by_cases hc:v∈C w
    · exact Or.inr hc
    · left
      intro he
      have hl:v∈rawReservedSpokeList π d σ w:=by
        have hs:retainedRawFamilyState π d σ false t J (v,w)=some (Sum.inr false):=hHold
        have hs':rawIntervalFamilyState π d σ (v,w)=some (Sum.inr false):=he ▸ hs
        simpa only [rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hs'
      exact hnot (hprotect w v hl hc)
  constructor
  · intro v
    have sub:Finset.univ.filter (fun w=>H false v w∧v∉R w\Y w)⊆
        (Finset.univ.filter (fun w=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w)))∪
        (Finset.univ.filter (fun w=>v∈C w)):=by
      intro w hw
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hw ⊢
      exact hpoint v w hw.1 hw.2
    have hn:= (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have hr:((Finset.univ.filter (fun w=>H false v w∧v∉R w\Y w)).card:ℝ)≤
        ((Finset.univ.filter (fun w=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w))).card:ℝ)+
        ((Finset.univ.filter (fun w=>v∈C w)).card:ℝ):=by exact_mod_cast hn
    linarith [hrow v]
  · intro w
    have sub:Finset.univ.filter (fun v=>H false v w∧v∉R w\Y w)⊆
        (Finset.univ.filter (fun v=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w)))∪C w:=by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hv ⊢
      exact hpoint v w hv.1 hv.2
    have hn:=(Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have hr:((Finset.univ.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤
        ((Finset.univ.filter (fun v=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w))).card:ℝ)+(C w).card:=by exact_mod_cast hn
    linarith [hcol w]
end Oberwolfach
