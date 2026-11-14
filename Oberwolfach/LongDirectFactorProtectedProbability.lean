module

public import Oberwolfach.LongTerminalSameSampleProtectedPreparation
public import Oberwolfach.ExpandedSamplePreparationProbabilityTransferAligned

@[expose] public section
/-! Transfer a common event whose corrected chain already gives the factors
for every admissible edit of the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longDirectProbabilityFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longDirectProbabilitySix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_terminal_direct_factor_protected_preparation
    {n qCount:ℕ} [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (F:Fin qCount→SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (z:MarkedExpandedActualOutcome (U:=Fin qCount) π d)
    (I:Finset (Fin n)) (Hubs:Finset (Fin qCount)) (γLoss σLoss:ℝ) (e₀:ℕ)
    (X:Finset (Fin n)) (Z:Finset (Fin qCount))
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×Fin qCount))) (ξ:ℝ)
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 I Hubs γLoss σLoss e₀ X Z D₀ C)
    (hFactor:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin qCount))→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→HasFactorDecomposition S F):
    ProtectedFactorPreparation P (longPhysicalStateGraph P z.1 {0,1,2,3,4}) I ξ e₀ F :=by
  unfold ProtectedFactorPreparation
  simpa only [Fintype.card_fin] using
    long_terminal_robust_preparation_certificate P π d r z I Hubs γLoss σLoss e₀ X Z D₀ C ξ qCount F hTerminal hFactor

theorem long_direct_factor_protected_probability
    {n qCount:ℕ} [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (F:Fin qCount→SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d)
    (I:Finset (Fin n)) (Hubs:Finset (Fin qCount)) (γLoss σLoss:ℝ) (e₀:ℕ)
    (X:Finset (Fin n)) (Z:Finset (Fin qCount)) (ξ:ℝ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (ρ:ℝ) (hρ:0≤ρ) (hρ1:ρ≤1) (hphysical:2*p+2*k+2*p₂+2*k₂+u=ρ)
    (q:Fin qCount→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:Fin qCount→Bool→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (ν:∀ω:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,
      FiniteLaw (StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false))))
    (Good:MarkedExpandedActualOutcome (U:=Fin qCount) π d→Prop) (b:ℝ)
    (hPointwise:∀z,Good z→∃(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
      (C:Finset (Finset (Fin n)⊕(Fin n×Fin qCount))),
      longTerminalProtectedReserve P π d r z z.2 I Hubs γLoss σLoss e₀ X Z D₀ C ∧
      ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin qCount))→
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
        (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
        markedResourceRimGraph C≤S→HasFactorDecomposition S F):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    b≤(μ.sigma ν).probability Good→
    b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ hρ hρ1)).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ e₀ F) :=by
  intro μ hGood
  have htransfer:(b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin
      (2*p+2*k+2*p₂+2*k₂+u) (by positivity) hsum)).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ e₀ F)):=by
    apply expanded_sample_preparation_probability_transfer_aligned P I ξ e₀ F p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν b
    apply hGood.trans
    apply finiteLaw_probability_mono
    intro z hz
    obtain ⟨D₀,C,hTerminal,hFactor⟩:=hPointwise z hz
    exact long_terminal_direct_factor_protected_preparation P F π d r z I Hubs γLoss σLoss e₀ X Z D₀ C ξ hTerminal hFactor
  simpa only [hphysical] using htransfer
end Oberwolfach
