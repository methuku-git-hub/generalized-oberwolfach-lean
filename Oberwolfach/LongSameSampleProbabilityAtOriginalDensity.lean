module

public import Oberwolfach.LongSameSampleProtectedProbabilityTransfer

@[expose] public section
/-! Preserve the original retention density when the assigned sample's
physical marginals sum to that density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longOriginalDensityFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longOriginalDensitySix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_same_sample_probability_at_original_density
    {n D:ℕ} [Nonempty (Fin n)] (hEven:Even D)
    (P:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (I:Finset (Fin n)) (Hubs:Finset (Fin (D/2))) (γLoss σLoss:ℝ) (e₀:ℕ)
    (X:Finset (Fin n)) (Z:Finset (Fin (D/2))) (ξ:ℝ)
    (K:ℕ) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (ρ:ℝ) (hρ:0≤ρ) (hρ1:ρ≤1) (hphysical:2*p+2*k+2*p₂+2*k₂+u=ρ)
    (q:Fin (D/2)→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:Fin (D/2)→Bool→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (ν:∀ω:∀e:RawWheelCoordinate (Fin n) (Fin (D/2)),RawExpandedMarkedCoordinateState Bool Bool e,
      FiniteLaw (StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false))))
    (Good:MarkedExpandedActualOutcome (U:=Fin (D/2)) π d→Prop) (b:ℝ)
    (hPointwise:∀z,Good z→∃(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
      (C:Finset (Finset (Fin n)⊕(Fin n×Fin (D/2)))),
      longTerminalProtectedReserve P π d r z z.2 I Hubs γLoss σLoss e₀ X Z D₀ C ∧
      LongTerminalMatchingFactorContinuationAt P F hF π d r z I ξ K θ Dmatch alpha γ eps Δ βList weight w D₀ C):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    b≤(μ.sigma ν).probability Good→
    b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ hρ hρ1)).probability (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ e₀ F) :=by
  intro μ hGood
  have h:=long_same_sample_protected_probability_transfer hEven P F hF π d r hd hnoshort I Hubs γLoss σLoss e₀ X Z ξ
    K θ Dmatch alpha γ eps Δ βList weight w p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS ν Good b hPointwise hGood
  simpa only [hphysical] using h
end Oberwolfach
