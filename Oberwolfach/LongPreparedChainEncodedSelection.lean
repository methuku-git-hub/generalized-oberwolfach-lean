module

public import Oberwolfach.LongBoundaryPreparedClasses
public import Oberwolfach.LongTerminalProtectedSelectedEncodedSplitLoad
public import Oberwolfach.LongFixedAbsorberSelectedRim

@[expose] public section
/-! Preserve a chain predicate while preparing the exact selected reserve for
    the encoded factor-complement and residual-orientation construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_prepared_chain_encoded_selection
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (gammaLoss sigmaLoss ξClass Δ:ℝ) (e₀:ℕ) (X₀:Finset (Fin n)) (Z₀:Finset U)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep ρreserve:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Chain:∀D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)),
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
      gammaLoss sigmaLoss e₀ X₀ Z₀ D₀ C)
    (hChain:Chain D₀ C)
    (hScale:(e₀:ℝ)≤ρreserve*n)
    (hPrepared:LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
      lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C):
    ∃D:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)),
    ∃C':Finset (Finset (Fin n)⊕(Fin n×U)),
      (longTerminalProtectedReserve P π d r z z.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
        gammaLoss sigmaLoss e₀ X₀ Z₀ D C' ∧ D=D₀ ∧ C'=C ∧ Chain D C') ∧
      markedResourceRimGraph C'≤longSelectedPhysicalGraph P π d z.1 ∧
      (C'.card:ℝ)≤ρreserve*n ∧
      (∀S:SimpleGraph (Fin n),S≤P → S.IsRegularOfDegree (2*Fintype.card U) →
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) →
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) →
      markedResourceRimGraph C'≤S →
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Q.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D C' S M Del ∧
        FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π Dv mm d (r+4) β ε Q F hF θ lamAssign eps δlocal δglobal αMatch bmatch ρ₀ ξPrep Δ a γ weight w z.1
          (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2) :=by
  refine ⟨D₀,C,⟨hTerminal,rfl,rfl,hChain⟩,?_,?_,hPrepared⟩
  · exact long_fixed_absorber_rim_is_selected P π d (r+4) z.1 false
      (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 false C X₀ Z₀ hTerminal.2.2.2
  · exact (Nat.cast_le.mpr hTerminal.2.1).trans hScale
end Oberwolfach
