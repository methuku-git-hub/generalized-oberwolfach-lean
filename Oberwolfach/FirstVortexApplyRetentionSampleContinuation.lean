module

public import Oberwolfach.FirstVortexApplySampleContinuation
public import Oberwolfach.FirstVortexCallerRetentionChangeChoice

@[expose] public section
/-! Apply the later chain to the selector's actual concentration event and
sampling probabilities, preserving any remaining continuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance applyRetentionSampleFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) applyRetentionSampleSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem first_vortex_apply_retention_sample_continuation
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
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Result:ℝ→ℝ→Prop):
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
    (0<K→θ≤1→∀ζRet:ℝ,0<active→0<ε→ε≤1/4→0<mm→0≤ζRet→ζRet≤active/128→ζret≤ζRet*ε/2→
      ∀p₂' k₂' u':ℝ,
      (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-(∑w,q w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
      (∀j v,|((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂' k₂' u' j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
      0≤γ→0≤θ→u'≤2*θ→
      (∀v,|(sampledColourDegree P (fun e=>(σ e).1) 4 v:ℝ)-u'*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
      ∀ζChange:ℝ,0≤ζChange→ζChange≤capStable→active≤ζChange→(min cap (1:ℝ))/2≤ζChange→
        0≤cLocal→active≤cLocal→Result ζRet ζChange)→
    ∃ζRet ζChange:ℝ,0≤ζRet ∧ ζRet≤active/128 ∧ ζret≤ζRet*ε/2 ∧
      0≤ζChange ∧ ζChange≤capStable ∧ active≤ζChange ∧ (min cap (1:ℝ))/2≤ζChange ∧ Result ζRet ζChange :=by
  intro m ρ p k q p₂ k₂ u σ hStart hOrient hApply
  obtain ⟨ζRet,ζChange,hRet0,hRetCap,hRetRate,hChange0,hChangeCap,hChangeActive,hChangeGlobal,hLocal0,hLocalActive⟩:=
    first_vortex_caller_retention_change_choice r d ε active θ t c ζret ζlocal ηBalance κaux cap capStable cLocal
      hret hactive hcap hcapStable hactiveGlobal hactiveLocal
  refine ⟨ζRet,ζChange,hRet0,hRetCap,hRetRate,hChange0,hChangeCap,hChangeActive,hChangeGlobal,?_⟩
  apply first_vortex_apply_sample_continuation hn hK hD P π d r F hF θ ρ₀ γ hθ hθ1 hρ₀ hγ hρlo hρhi z (Result ζRet ζChange) hStart hOrient
  intro p₂' k₂' u' hStart' hIn hγ' hθ' hu hDeg
  exact hApply hK hθ1 ζRet hactive hε hε1 hmm hRet0 hRetCap hRetRate p₂' k₂' u' hStart' hIn hγ' hθ' hu hDeg
    ζChange hChange0 hChangeCap hChangeActive hChangeGlobal hLocal0 hLocalActive
end Oberwolfach
