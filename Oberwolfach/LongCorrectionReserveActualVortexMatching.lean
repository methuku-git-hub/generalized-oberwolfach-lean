module

public import Oberwolfach.LongCorrectionReserveActualVortexChain

@[expose] public section
/-! Retain the matching on the very deletion and absorber reserve that
support the corrected-sample restrictions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_correction_reserve_actual_vortex_matching
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L a₀ b₀ e₀ Bpart:ℕ) (hB:e₀≤Bpart) (gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (h:LongCorrectionReserveUniversalEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀)
    (hPrepared:∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
      (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C):
    LongSampleChainMatchingEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
      θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
      (LongCorrectedReserveVortexChainEvent P π d r Dv mm β ε Q hpres L gammaLoss sigmaLoss extra) :=by
  obtain ⟨D₀,hvalid,havoid,C,hdisF,hcard,hrows,hhubs,habsCorr,habsRaw,hmatch,D₂,hvalid₂,hremoved,hremaining,hdis⟩:=h
  refine ⟨D₀,hvalid,C,hcard.trans hB,hdis,?_,hmatch,hPrepared D₀ C.edges hmatch⟩
  refine ⟨habsCorr,habsRaw,?_,D₂,hvalid₂,hremoved,hremaining,hdis,?_⟩
  · exact marked_vortex_finite_sample_chain_exists Q π hpres _ _ Q.length Q.length_pos
  · exact marked_vortex_finite_sample_chain_exists Q π hpres _ _ Q.length Q.length_pos
end Oberwolfach
