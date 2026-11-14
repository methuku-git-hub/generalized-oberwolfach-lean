module

public import Oberwolfach.LongTerminalSameSampleFactorContinuation
public import Oberwolfach.ProtectedFactorPreparation

@[expose] public section
/-! The same-sample long continuation supplies the original protected
factor-preparation interface for every admissible edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longTerminalPrepFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance (priority := 2000) longTerminalPrepSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_terminal_same_sample_protected_preparation
    {n D:ℕ} [Nonempty (Fin n)] (hEven:Even D)
    (P:SimpleGraph (Fin n)) (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d r:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:MarkedExpandedActualOutcome (U:=Fin (D/2)) π d)
    (I:Finset (Fin n)) (Hubs:Finset (Fin (D/2))) (γLoss σLoss:ℝ) (e₀:ℕ)
    (X:Finset (Fin n)) (Z:Finset (Fin (D/2)))
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×Fin (D/2)))) (ξ:ℝ)
    (K:ℕ) (θ Dmatch alpha γ eps Δ βList:ℝ)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 I Hubs γLoss σLoss e₀ X Z D₀ C)
    (hContinuation:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin (D/2)))→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
        LongClassMatchingDeletionWitness Δ P π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del ∧
        LongMatchingSameSampleFactorDataAt S P F π d r z M):
    ProtectedFactorPreparation P (longPhysicalStateGraph P z.1 {0,1,2,3,4}) I ξ e₀ F :=by
  unfold ProtectedFactorPreparation
  simpa only [Fintype.card_fin] using
    long_terminal_same_sample_factor_continuation hEven P F hF π d r hd hnoshort z I Hubs γLoss σLoss e₀ X Z D₀ C ξ K θ Dmatch alpha γ eps Δ βList weight w hTerminal hContinuation
end Oberwolfach
