module

public import Oberwolfach.LongBoundaryPreparedClasses
public import Oberwolfach.LongTerminalProtectedSelectedEncodedSplitLoad
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Extend the chain-selected terminal reserve pointwise, retaining the same
    outcome, correction, reserve and probability bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

def LongTerminalPreparedChainEvent
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (gammaLoss sigmaLoss ξClass Δ:ℝ) (e₀ L:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Chain:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))→
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop):Prop :=
  ∃D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)),
  ∃C:Finset (Finset (Fin n)⊕(Fin n×U)),
    longTerminalProtectedReserve P π d r z z.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
      gammaLoss sigmaLoss e₀ (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) D₀ C ∧
    LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
      lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C ∧
    Chain z D₀ C

theorem long_terminal_prepared_chain_extend_probability
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (gammaLoss sigmaLoss ξClass Δ:ℝ) (e₀ L:ℕ)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Chain Continue:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))→
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop)
    (Prior:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (hContinue:∀z:MarkedExpandedActualOutcome (U:=U) π d,Prior z→
      ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      longTerminalProtectedReserve P π d r z z.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
        gammaLoss sigmaLoss e₀ (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C→
      Chain z D₀ C→Continue z D₀ C)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d)) (bProb:ℝ):
    bProb≤μ.probability (fun z=>Prior z ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w Chain)→
    bProb≤μ.probability (fun z=>Prior z ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
          (fun z D₀ C=>Chain z D₀ C ∧ Continue z D₀ C)) :=by
  intro hprob
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨hp,D₀,C,hterm,hprep,hchain⟩:=hz
  exact ⟨hp,D₀,C,hterm,hprep,hchain,hContinue z hp D₀ C hterm hprep hchain⟩
end Oberwolfach
