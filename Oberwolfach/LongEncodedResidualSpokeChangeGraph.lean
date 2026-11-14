module

public import Oberwolfach.LongCorrectedSpokeGraphFromDivisibility
public import Oberwolfach.MarkedReferenceFullSpokeBalance
public import Oberwolfach.MarkedEncodedHostIncomingDegreeChange

@[expose] public section
/-! Assemble the spoke change graph from the reference balance, the
same-sample encoded residual, and exact corrected divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance encodedResidualSpokeGraphFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_encoded_residual_spoke_change_graph
    {n:ℕ} {U E K:Type} [Fintype U] [DecidableEq U] [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K]
    (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw σ τ:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ lossRow lossCol ε η ζ:ℝ)
    (tail head:E→Fin n) (ktail khead:K→Fin n)
    (hE:Function.Injective (fun e=>(tail e,head e)))
    (hK:Function.Injective (fun e=>(ktail e,khead e)))
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ):
    let ρ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d ρ false t J false false
    let H₀:=fun v w=>v∈R w\Y w
    let HK:=retainedRawMarkedSpokes π d ρ false t J false true true
    let H':Bool→Fin n→U→Prop:=fun b v w=>if b then HK v w else H₀ v w;
    (∀v w,¬(H₀ v w∧HK v w))→
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun z:Fin n×U=>H₀ z.1 z.2∨HK z.1 z.2)) m→
    MarkedRestrictedBalanceWithSpokes G π d m Finset.univ Finset.univ ε σ H→
    (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:K,ktail e=x∧khead e=y else ∃e:E,tail e=x∧head e=y)→
    ∀FR:SimpleGraph (Fin n),
    (∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀v,(FR.degree v:ℝ)≤η)→
    (∀v,((Finset.univ.filter (fun w=>retainedRawFamilyState π d ρ false t J (v,w)≠rawIntervalFamilyState π d ρ (v,w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>retainedRawFamilyState π d ρ false t J (v,w)≠rawIntervalFamilyState π d ρ (v,w))).card:ℝ)≤lossCol)→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(ε+2*η)≤ζ*n→
    2*(lossCol+10*θ*n)+ε≤ζ*n→
    ∃FS:SimpleGraph (Fin n⊕U),
      (∀b v w,¬(H b v w↔H' b v w)→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
      ∀z,(FS.degree z:ℝ)≤ζ*n:=by
  intro ρ Y H H₀ HK H' hdis hdiv hbalance hrim FR hchange hFR hRetRow hRetCol hBudgetRow hBudgetCol
  have hb:=marked_reference_full_spoke_balance G π d m ε σ H hbalance
  let oldRim:=fun v:Fin n=>(markedRestrictedDegree G π (3*d) (fun e=>σ (Sum.inl e)) false true v Finset.univ:ℝ)+
    (markedRestrictedDegree G π (3*d) (fun e=>σ (Sum.inl e)) true true v Finset.univ:ℝ)
  have hr:=marked_encoded_host_incoming_degree_change G π d σ τ tail head ktail khead hE hK hrim FR η hchange hFR
  exact long_corrected_spoke_graph_from_divisibility π d m raw t J R θ δ lossRow lossCol ε ε (2*η) ζ tail head ktail khead hcontrol
    hdis (by convert hdiv using 1 <;> congr!) hRetRow hRetCol oldRim hb.1 hr hb.2 hBudgetRow hBudgetCol
end Oberwolfach
