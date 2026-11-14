module

public import Oberwolfach.LongResidualReservedSpokeLossByAgreement
public import Oberwolfach.MarkedSpokeRowSizeFromBalance

@[expose] public section
/-! The actual corrected spoke partition admits a physical change graph
with a degree bound obtained from retention, completion and balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance correctedSpokeChangeByAgreementFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_corrected_spoke_change_graph_by_agreement
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ lossRow lossCol εrow εcol δrim ζ:ℝ)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ):
    let σ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d σ false t J false false
    let H':Bool→Fin n→U→Prop:=fun b v w=>if b then retainedRawMarkedSpokes π d σ false t J false true true v w else v∈R w\Y w;
    (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossCol)→
    ∀oldRim newRim:Fin n→ℝ,
    (∀v,|oldRim v-(((Finset.univ.filter (fun w=>H false v w)).card:ℝ)+((Finset.univ.filter (fun w=>H true v w)).card:ℝ))|≤εrow)→
    (∀v,newRim v=((Finset.univ.filter (fun w=>H' false v w)).card:ℝ)+((Finset.univ.filter (fun w=>H' true v w)).card:ℝ))→
    (∀v,newRim v-oldRim v≤δrim)→
    (∀w,|((Finset.univ.filter (fun v=>H false v w)).card:ℝ)-(m:ℝ)*(Finset.univ.filter (fun v=>H true v w)).card|≤εcol)→
    (∀w,(Finset.univ.filter (fun v=>H' false v w)).card=m*(Finset.univ.filter (fun v=>H' true v w)).card)→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(εrow+δrim)≤ζ*n→
    2*(lossCol+10*θ*n)+εcol≤ζ*n→
    ∃FS:SimpleGraph (Fin n⊕U),
      (∀b v w,¬(H b v w↔H' b v w)→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
      ∀z,(FS.degree z:ℝ)≤ζ*n:=by
  intro σ Y H H' hRetRow hRetCol oldRim newRim hOldRow hNewRow hRim hOldCol hNewCol hRowBudget hColBudget
  have hmark:∀v w,H true v w↔H' true v w:=by intro v w;rfl
  have ⟨hlrow,hlcol⟩:=long_residual_reserved_spoke_loss_by_agreement π d raw t J R θ δ hcontrol
  have hLossRow:∀v,((Finset.univ.filter (fun w=>H false v w∧¬H' false v w)).card:ℝ)≤lossRow+(δ*n+(Real.sqrt δ*n+1)):=by
    intro v
    have hh:=hlrow v
    change ((Finset.univ.filter (fun w=>H false v w∧¬H' false v w)).card:ℝ)≤_ at hh
    linarith [hRetRow v]
  have hLossCol:∀w,((Finset.univ.filter (fun v=>H false v w∧¬H' false v w)).card:ℝ)≤lossCol+10*θ*n:=by
    intro w
    have hh:=hlcol w
    change ((Finset.univ.filter (fun v=>H false v w∧¬H' false v w)).card:ℝ)≤_ at hh
    linarith [hRetCol w]
  have hSizeRow:=marked_spoke_row_size_from_balance H H' oldRim newRim εrow δrim hmark hOldRow (by intro v; convert hNewRow v using 1 <;> congr!) hRim
  have hSizeCol:=marked_spoke_column_size_from_balance H H' m εcol hmark hOldCol (by intro w; convert hNewCol w using 1 <;> congr!)
  have hdeg:=marked_spoke_change_from_loss_and_size H H' hmark
    (lossRow+(δ*n+(Real.sqrt δ*n+1))) (εrow+δrim) (lossCol+10*θ*n) εcol
    (by intro v; convert hLossRow v using 1 <;> congr!)
    (by intro v; convert hSizeRow v using 1 <;> congr!)
    (by intro w; convert hLossCol w using 1 <;> congr!)
    (by intro w; convert hSizeCol w using 1 <;> congr!)
  refine ⟨markedSpokeChangeGraph H H',?_,?_⟩
  · intro b v w h
    exact (marked_spoke_change_graph_adj H H' v w).mpr ⟨b,h⟩
  · intro z
    cases z with
    | inl v => exact (hdeg.1 v).trans hRowBudget
    | inr w => exact (hdeg.2 w).trans hColBudget
end Oberwolfach
