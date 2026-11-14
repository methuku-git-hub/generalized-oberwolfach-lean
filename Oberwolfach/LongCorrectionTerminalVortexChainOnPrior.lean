module

public import Oberwolfach.LongCorrectionReserveUniversalOnPrior
public import Oberwolfach.LongCorrectionTerminalPreparedVortexChain
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Two high-probability requirements can be joined to an arbitrary prior on
the same expanded outcome before choosing correction, reserve and matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_correction_terminal_vortex_chain_on_prior
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length) (hreg:P.IsRegularOfDegree Dv) (hn:0<n) (hD:0<Dv)
    (hρhi:initialIndexDensity U Dv≤1) (hε:0≤ε)
    (αHost:ℝ) (hsmall:ε≤αHost/100000)
    (size a₀ b₀ e₀ f₀ Bpart:ℕ) (εAbs ζCorr ξCorr gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (heAbs:ε≤εAbs) (hsize:2*mm≤size) (hξ:0≤ξCorr)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n))
    (hExtra:(e₀:ℝ)≤extra*n) (hB:e₀≤Bpart)
    (θ a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (F₀:MarkedExpandedActualOutcome (U:=U) π d→Finset (Finset (Fin n)⊕(Fin n×U)))
    (hF₀:∀z,(F₀ z).card≤f₀)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (E:MarkedExpandedActualOutcome (U:=U) π d→Prop) (εE εC εM:ℝ)
    (lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep:ℝ)
    (hPrepared:∀z:MarkedExpandedActualOutcome (U:=U) π d,E z→
      ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C):
    let Corr:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
      let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
      let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
      MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H
        (Q.extendedVertices 1) (Q.extendedIndices 1)
    let Match:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
      LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1) (Q.extendedIndices 1)
        K Bpart θ Dv a γ eps βList F hF weight w;
    1-εE≤μ.probability E→1-εC≤μ.probability Corr→1-εM≤μ.probability Match→
    1-(εE+εC)-εM≤μ.probability (fun z=>E z ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
        (LongCorrectedReserveVortexChainEvent P π d r Dv mm β ε Q hpres L gammaLoss sigmaLoss extra)) :=by
  intro Corr Match hE hC hM
  have hp:=long_correction_reserve_universal_on_prior P π d r Dv mm β ε Q hpres L hL hreg hn hD hρhi hε
    αHost hsmall size a₀ b₀ e₀ f₀ Bpart εAbs ζCorr ξCorr gammaLoss sigmaLoss extra ξClass Δ heAbs hsize hξ hbudget hExtra hB
    θ a γ eps βList F hF weight w F₀ hF₀ μ E εE εC εM hE hC hM
  apply hp.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  exact long_correction_terminal_prepared_vortex_chain P π d r Dv mm β ε Q hpres L a₀ b₀ e₀ Bpart hB
    gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep
    F hF weight w (F₀ z) hz.2 (hPrepared z hz.1)
end Oberwolfach
