module

public import Oberwolfach.MarkedEncodedIncomingDegreeOnRoots
public import Oberwolfach.LongOutsideSpokeChangesFromGlobalBalance
public import Oberwolfach.LongEncodedResidualSpokeGraphByAgreement
public import Oberwolfach.LongCorrectedSpokeGraphDivisibleByAgreement
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
local instance encodedResidualSpokeGraphOutsideFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_encoded_residual_spoke_change_graph_with_outside_control
    {n:ℕ} {U E K:Type} [Fintype U] [DecidableEq U] [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K]
    (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw σ τ:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ lossRow lossCol ε η ζ:ℝ)
    (tail head:E→Fin n) (ktail khead:K→Fin n)
    (hE:Function.Injective (fun e=>(tail e,head e)))
    (hK:Function.Injective (fun e=>(ktail e,khead e)))
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ)
    (I:Finset (Fin n)) (C:U→Finset (Fin n)) (ζret load ηLocal:ℝ) (hζret:0≤ζret) (hU:Fintype.card U≤n):
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
    (∀v,π v∈I↔v∈I)→
    RetainedRestrictionGood π d ρ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret J→
    (∀w v,v∈rawReservedSpokeList π d ρ w→v∉C w→v∈R w\Y w)→
    (∀v,v∉I→((Finset.univ.filter (fun w=>v∈C w)).card:ℝ)≤load)→
    (∀v,v∉I→(FR.degree v:ℝ)≤ηLocal)→
    (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossCol)→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(ε+2*η)≤ζ*n→
    2*(lossCol+10*θ*n)+ε≤ζ*n→
    ∃FS:SimpleGraph (Fin n⊕U),
      (∀b v w,¬(H b v w↔H' b v w)→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
      (∀z,(FS.degree z:ℝ)≤ζ*n) ∧
      ∀B:Finset U,∀v,v∉I→
        (∑w∈B,if ¬(H false v w↔H' false v w) then (1:ℝ) else 0)≤
          2*(ζret*n+load)+(ε+2*ηLocal):=by
  intro ρ Y H H₀ HK H' hdis hdiv hbalance hrim FR hchange hFR hI hgood hprotect hload hFRlocal hRetRow hRetCol hBudgetRow hBudgetCol
  obtain ⟨FS,hSpoke,hFS⟩:=long_encoded_residual_spoke_change_graph_by_agreement G π d m raw σ τ t J R θ δ lossRow lossCol ε η ζ
    tail head ktail khead hE hK hcontrol hdis hdiv hbalance hrim FR hchange hFR hRetRow hRetCol hBudgetRow hBudgetCol
  let Roots:Finset (Fin n):=Finset.univ\I
  have hRoots:∀x,x∈Roots→π x∈Roots:=by
    intro x hx
    have hn:x∉I:=(Finset.mem_sdiff.mp hx).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h=>hn ((hI x).mp h)⟩
  have hFR':∀v∈Roots,(FR.degree v:ℝ)≤ηLocal:=by
    intro v hv
    exact hFRlocal v (Finset.mem_sdiff.mp hv).2
  let oldRim:=fun v:Fin n=>(markedRestrictedDegree G π (3*d) (fun e=>σ (Sum.inl e)) false true v Finset.univ:ℝ)+
    (markedRestrictedDegree G π (3*d) (fun e=>σ (Sum.inl e)) true true v Finset.univ:ℝ)
  let newRim:=fun v:Fin n=>((Finset.univ.filter (fun e:E⊕K=>Sum.elim head khead e=v)).card:ℝ)
  have hb:=marked_reference_full_spoke_balance G π d m ε σ H hbalance
  have hr:=marked_encoded_host_incoming_degree_change_on_roots G π d σ τ tail head ktail khead hE hK hrim FR Roots hRoots ηLocal hchange hFR'
  obtain ⟨hrow,_⟩:=marked_divisible_full_spoke_size_identities tail head ktail khead H₀ HK m hdis (by convert hdiv using 1 <;> congr!)
  have hNew:∀v,v∉I→newRim v=((Finset.univ.filter (fun w=>v∈R w\Y w)).card:ℝ)+
      ((Finset.univ.filter (fun w=>H true v w)).card:ℝ):=by
    intro v _
    convert hrow v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  have hLocal:=long_outside_spoke_changes_from_global_balance π d raw t J I R C ζret load ε (2*ηLocal)
    hζret hU hgood hprotect hload oldRim newRim (by intro v _;exact hb.1 v) hNew
    (by intro v hv;exact hr v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩))
  refine ⟨FS,hSpoke,hFS,?_⟩
  intro B v hv
  convert hLocal B v hv using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
