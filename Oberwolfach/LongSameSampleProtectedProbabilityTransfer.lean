module

public import Oberwolfach.LongTerminalSameSampleProtectedPreparation
public import Oberwolfach.ExpandedSamplePreparationProbabilityTransferAligned

@[expose] public section
/-! A high-probability event on the original expanded sample transfers the
same-sample long continuation to the original independent-retention law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSameSampleTransferFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longSameSampleTransferSix:DecidableEq (Fin 6):=instDecidableEqFin 6

def LongTerminalMatchingFactorContinuationAt
    {n D:ℕ} [Nonempty (Fin n)] (P:SimpleGraph (Fin n))
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (z:MarkedExpandedActualOutcome (U:=Fin (D/2)) π d)
    (I:Finset (Fin n)) (ξ:ℝ) (K:ℕ) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×Fin (D/2)))):Prop :=
  ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin (D/2)))→
    (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
    markedResourceRimGraph C≤S→
    ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      LongClassMatchingDeletionWitness Δ P π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del ∧
      LongMatchingSameSampleFactorDataAt S P F π d r z M

theorem long_same_sample_protected_probability_transfer
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
    b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (2*p+2*k+2*p₂+2*k₂+u)
      (by positivity) hsum)).probability (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ e₀ F) :=by
  intro μ hGood
  apply expanded_sample_preparation_probability_transfer_aligned P I ξ e₀ F p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν b
  apply hGood.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨D₀,C,hTerminal,hContinuation⟩:=hPointwise z hz
  exact long_terminal_same_sample_protected_preparation hEven P F hF π d r hd hnoshort z I Hubs γLoss σLoss e₀ X Z D₀ C ξ K θ Dmatch alpha γ eps Δ βList weight w hTerminal hContinuation
end Oberwolfach
