module

public import Oberwolfach.FirstVortexSelectedClassRetentionSampleExact
public import Oberwolfach.FirstVortexConcreteUniversalMatchedOutcome
public import Oberwolfach.FirstVortexCallerRetentionChangeChoice

@[expose] public section
/-! Apply the later chain to the selector's actual concentration event and
sampling probabilities, preserving any remaining continuation. -/
/-! The same sample consequence without the unnecessary universal
regular-completion event; all actual target hypotheses are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance actualMatchingRetentionFixedClassExactFinNoCompletion (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) actualMatchingRetentionFixedClassExactSixNoCompletion:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem first_vortex_actual_matching_retention_fixed_class_no_completion
    {n K D:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (hD:0<D)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ₀ γ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (hρ₀:0<ρ₀) (hγ:0≤γ)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (ε active t c ζret ζlocal ηBalance κaux cap capStable cLocal:ℝ) (mm:ℕ)
    (hε:0<ε) (hε1:ε≤1/4) (hmm:0<mm)
    (hret:FirstVortexRetentionBalanceRates r d ε active θ t c ζret ζlocal ηBalance κaux)
    (hactive:0<active) (hcap:0<cap) (hcapStable:cap≤capStable)
    (hactiveGlobal:active≤(min cap (1:ℝ))/2) (hactiveLocal:active≤cLocal)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (β:ℝ) (Vort:Vortex U P D β ε mm)
    (αHost ξClass γLoss σLoss:ℝ) (hsmall:ε≤αHost/100000) (L e₀:ℕ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
      γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C)
    (lamAssign epsOrd δlocal δglobal α bmatch ξ Δ a βList:ℝ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Result:SimpleGraph (Fin n)→(Fin n→Fin n→ℕ)→SimpleGraph (Fin n)→ℝ→ℝ→Prop):
    let Match:=fun (S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n))=>
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ D a γ epsOrd βList F hF weight w D₀ C S M Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π D mm d (r+4) β ε Vort F hF θ lamAssign epsOrd δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2
    let m:ℝ:=(r+4:ℕ)
    let ρ:=initialIndexDensity U D
    let p:ℝ:=ρ*(1/100)/2
    let k:ℝ:=ρ*((1/100)/m)/2
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let p₂:ℝ:=(∑w,longAssignedApproxOrdinaryWeight F hF K (r+4) θ w)/(D:ℝ)
    let k₂:ℝ:=(∑w,longAssignedApproxMarkedWeight F hF K (r+4) θ w)/(D:ℝ)
    let u:ℝ:=2*(∑w,(1-1/100-(1/100)/m-longAssignedApproxMarkedWeight F hF K (r+4) θ w-
      longAssignedApproxOrdinaryWeight F hF K (r+4) θ w))/(D:ℝ)
    let σ:=fun e:Sym2 (Fin n)=>z.1 (Sum.inl e);
    (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-(∑w,q w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀(j:Fin 6) (v:Fin n),
      |((∑x,sampledColourOrientation P σ j v x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(σ e).1) j v:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j*P.degree v|<(n:ℝ)^(3/5:ℝ))→
    (∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),Match S M Del ∧
    (0<K→θ≤1→∀ζRet:ℝ,0<active→0<ε→ε≤1/4→0<mm→0≤ζRet→ζRet≤active/128→ζret≤ζRet*ε/2→
      ∀p₂' k₂' u':ℝ,
      (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-(∑w,q w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
      (∀j v,|((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂' k₂' u' j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
      0≤γ→0≤θ→u'≤2*θ→
      (∀v,|(sampledColourDegree P (fun e=>(σ e).1) 4 v:ℝ)-u'*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
      ∀ζChange:ℝ,0≤ζChange→ζChange≤capStable→active≤ζChange→(min cap (1:ℝ))/2≤ζChange→
        0≤cLocal→active≤cLocal→Result S M Del ζRet ζChange) )→
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),Match S M Del ∧
      ∃ζRet ζChange:ℝ,0≤ζRet ∧ ζRet≤active/128 ∧ ζret≤ζRet*ε/2 ∧
        0≤ζChange ∧ ζChange≤capStable ∧ active≤ζChange ∧ (min cap (1:ℝ))/2≤ζChange ∧ ζChange=(min cap (1:ℝ))/2 ∧ Result S M Del ζRet ζChange :=by
  intro Match m ρ p k q p₂ k₂ u σ hStart hOrient hFor
  intro S hSP hregS hEditS hInnerS hReserveS
  obtain ⟨M,Del,hMatch,hApply⟩:=hFor S hSP hregS hEditS hInnerS hReserveS
  obtain ⟨ζRet,ζChange,hRet0,hRetCap,hRetRate,hChange0,hChangeCap,hChangeActive,hChangeGlobal,hExact,hResult⟩:=
    first_vortex_apply_retention_sample_exact hn hK hD P π d r F hF θ ρ₀ γ hθ hθ1 hρ₀ hγ hρlo hρhi
      ε active t c ζret ζlocal ηBalance κaux cap capStable cLocal mm hε hε1 hmm hret hactive hcap hcapStable
      hactiveGlobal hactiveLocal z (Result S M Del) hStart hOrient hApply
  exact ⟨M,Del,hMatch,ζRet,ζChange,hRet0,hRetCap,hRetRate,hChange0,hChangeCap,hChangeActive,hChangeGlobal,hExact,hResult⟩
end Oberwolfach
