module

public import Oberwolfach.LongSameSampleProbabilityAtOriginalDensity
public import Oberwolfach.LongAssignedPhysicalTotalOriginal

@[expose] public section
/-! Use the actual long-cycle assignment recipe to transfer a same-sample
terminal continuation to the original retention density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longAssignedPrepTransferFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longAssignedPrepTransferSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_assigned_same_sample_preparation_probability
    {n Dclass:ℕ} [Nonempty (Fin n)] (hn:0<n) (hEven:Even Dclass)
    (P:SimpleGraph (Fin n)) (F:Fin (Dclass/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d) (hm:7≤r+4)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (I:Finset (Fin n)) (Hubs:Finset (Fin (Dclass/2))) (γLoss σLoss:ℝ) (e₀:ℕ)
    (X:Finset (Fin n)) (Z:Finset (Fin (Dclass/2))) (ξ:ℝ)
    (K:ℕ) (hK:0<K) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100)
    (ρ₀ ρ Dhost:ℝ) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hDhost:0<Dhost)
    (hsize:ρ*Dhost=2*Fintype.card (Fin (Dclass/2)))
    (hcut:(1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ):
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
    ∀(ν:∀ω:∀e:RawWheelCoordinate (Fin n) (Fin (Dclass/2)),RawExpandedMarkedCoordinateState Bool Bool e,
      FiniteLaw (StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false))))
    (Good:MarkedExpandedActualOutcome (U:=Fin (Dclass/2)) π d→Prop) (bprob:ℝ),
    (∀z,Good z→∃(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
      (C:Finset (Finset (Fin n)⊕(Fin n×Fin (Dclass/2)))),
      longTerminalProtectedReserve P π d r z z.2 I Hubs γLoss σLoss e₀ X Z D₀ C ∧
      LongTerminalMatchingFactorContinuationAt P F hF π d r z I ξ K θ Dmatch alpha γ eps Δ βList weight w D₀ C)→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1 d hd q
      hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2);
    bprob≤(μ.sigma ν).probability Good→
    bprob≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ (hρ₀.le.trans hρlo) hρ1)).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ e₀ F) :=by
  intro b a p₁ k₁ p₂ k₂ udens q s hLaw ν Good bprob hPointwise μ hGood
  have hphysical:=long_assigned_physical_total_original hn F hF Allowed hAllowed K hK (r+4) d hm hd θ ρ₀ ρ Dhost
    hθ0 hθ hρ₀ hρlo hρ1 hDhost hsize hcut hclass
  exact long_same_sample_probability_at_original_density hEven P F hF π d r hd hnoshort I Hubs γLoss σLoss e₀ X Z ξ
    K θ Dmatch alpha γ eps Δ βList weight w p₁ k₁ p₂ k₂ udens hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1
    hLaw.2.2.2.2.2.1 ρ (hρ₀.le.trans hρlo) hρ1 hphysical q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1
    s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 ν Good bprob hPointwise hGood
end Oberwolfach
