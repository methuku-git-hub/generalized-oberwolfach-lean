module

public import Oberwolfach.LongCorrectedSpokeGraphByAgreement
public import Oberwolfach.MarkedDivisibleSpokeSizeIdentities

@[expose] public section
/-! Corrected wheel-divisibility supplies the exact spoke sizes needed by
the physical change-graph bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance spokeGraphDivisibilityByAgreementFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_corrected_spoke_graph_from_divisibility_by_agreement
    {n:ℕ} {U E K:Type} [Fintype U] [DecidableEq U] [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ lossRow lossCol εrow εcol δrim ζ:ℝ)
    (tail head:E→Fin n) (ktail khead:K→Fin n)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ):
    let σ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d σ false t J false false
    let H₀:=fun v w=>v∈R w\Y w
    let HK:=retainedRawMarkedSpokes π d σ false t J false true true
    let H':Bool→Fin n→U→Prop:=fun b v w=>if b then HK v w else H₀ v w;
    (∀v w,¬(H₀ v w∧HK v w))→
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun z:Fin n×U=>H₀ z.1 z.2∨HK z.1 z.2)) m→
    (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossCol)→
    ∀oldRim:Fin n→ℝ,
    (∀v,|oldRim v-(((Finset.univ.filter (fun w=>H false v w)).card:ℝ)+((Finset.univ.filter (fun w=>H true v w)).card:ℝ))|≤εrow)→
    (∀v,((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)-oldRim v≤δrim)→
    (∀w,|((Finset.univ.filter (fun v=>H false v w)).card:ℝ)-(m:ℝ)*(Finset.univ.filter (fun v=>H true v w)).card|≤εcol)→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(εrow+δrim)≤ζ*n→
    2*(lossCol+10*θ*n)+εcol≤ζ*n→
    ∃FS:SimpleGraph (Fin n⊕U),
      (∀b v w,¬(H b v w↔H' b v w)→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
      ∀z,(FS.degree z:ℝ)≤ζ*n:=by
  intro σ Y H H₀ HK H' hdis hdiv hRetRow hRetCol oldRim hOld hRim hOldCol hBudgetRow hBudgetCol
  obtain ⟨hrow,hcol⟩:=marked_divisible_full_spoke_size_identities tail head ktail khead H₀ HK m hdis (by convert hdiv using 1 <;> congr!)
  let newRim:=fun v:Fin n=>((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)
  have hNewRow:∀v,newRim v=((Finset.univ.filter (fun w=>H' false v w)).card:ℝ)+((Finset.univ.filter (fun w=>H' true v w)).card:ℝ):=by
    intro v
    convert hrow v using 1 <;> congr!
  have hNewCol:∀w,(Finset.univ.filter (fun v=>H' false v w)).card=m*(Finset.univ.filter (fun v=>H' true v w)).card:=by
    intro w
    convert hcol w using 1 <;> congr!
  exact long_corrected_spoke_change_graph_by_agreement π d m raw t J R θ δ lossRow lossCol εrow εcol δrim ζ hcontrol
    hRetRow hRetCol oldRim newRim hOld hNewRow hRim hOldCol hNewCol hBudgetRow hBudgetCol
end Oberwolfach
