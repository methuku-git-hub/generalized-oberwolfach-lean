module

public import Oberwolfach.LongActualRawLawParameters
public import Oberwolfach.LongAssignedPhysicalTotalOriginal
public import Oberwolfach.ExpandedSamplePreparationProbabilityTransferAligned

@[expose] public section
/-! Transfer a preparation probability for the assigned expanded sample
   to the exact original independent-retention density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longAssignedPreparationTransferFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) longAssignedPreparationTransferSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_assigned_preparation_probability_transfer
    {n qCount:ℕ} [Nonempty (Fin n)] (hn:0<n)
    (P:SimpleGraph (Fin n)) (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d) (hm:7≤r+4)
    (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (K:ℕ) (hK:0<K) (θ ρ₀ ρ Dhost:ℝ) (hθ0:0≤θ) (hθ:θ≤1/100)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hDhost:0<Dhost)
    (hsize:ρ*Dhost=2*Fintype.card (Fin qCount))
    (hcut:(1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(((r+4:ℕ):ℝ)))/2
    let p₂:=(∑u,b u)/Dhost
    let k₂:=(∑u,a u)/Dhost
    let udens:=2*(∑u,(1-1/100-(1/100)/(((r+4:ℕ):ℝ))-a u-b u))/Dhost
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let s:=longAssignedSpokeProbability F hF K (r+4) θ
    let hLaw:=long_assigned_actual_raw_law_parameters hn F hF Allowed hAllowed K hK (r+4) d hm hd θ ρ₀ ρ Dhost
      hθ0 hθ hρ₀ hρlo hρ1 hDhost hsize hcut hclass
    ∀(ν:∀ω:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,
      FiniteLaw (StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)))) (bprob:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1 d hd q
      hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2);
    bprob≤(μ.sigma ν).probability (fun z=>ProtectedFactorPreparation P (longPhysicalStateGraph P z.1 {0,1,2,3,4}) I ξ B F)→
    bprob≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ (hρ₀.le.trans hρlo) hρ1)).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  intro b a p₁ k₁ p₂ k₂ udens q s hLaw ν bprob μ hprob
  have hphysical:=long_assigned_physical_total_original hn F hF Allowed hAllowed K hK (r+4) d hm hd θ ρ₀ ρ Dhost
    hθ0 hθ hρ₀ hρlo hρ1 hDhost hsize hcut hclass
  change 2*p₁+2*k₁+2*p₂+2*k₂+udens=ρ at hphysical
  have h:=expanded_sample_preparation_probability_transfer_aligned P I ξ B F p₁ k₁ p₂ k₂ udens
    hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1 d hd q
    hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 ν bprob hprob
  have hcoin_congr:∀(p q:ℝ) (hp0:0≤p) (hp1:p≤1) (hq0:0≤q) (hq1:q≤1),p=q→
      FiniteLaw.retentionCoin p hp0 hp1=FiniteLaw.retentionCoin q hq0 hq1:=by
    intro p q hp0 hp1 hq0 hq1 hpq
    subst q
    rfl
  have hNonneg:0≤2*p₁+2*k₁+2*p₂+2*k₂+udens:=by
    rw [hphysical]
    exact hρ₀.le.trans hρlo
  have hcoin:=hcoin_congr (2*p₁+2*k₁+2*p₂+2*k₂+udens) ρ hNonneg
    hLaw.2.2.2.2.2.1 (hρ₀.le.trans hρlo) hρ1 hphysical
  have hpi:(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (2*p₁+2*k₁+2*p₂+2*k₂+udens) hNonneg hLaw.2.2.2.2.2.1)) =
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ (hρ₀.le.trans hρlo) hρ1)):=by
    congr 1
    funext e
    exact hcoin
  simpa only [hpi] using h
end Oberwolfach
