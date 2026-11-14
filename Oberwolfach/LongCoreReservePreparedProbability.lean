module

public import Oberwolfach.LongCorrectionReserveConcreteClassEvent
public import Oberwolfach.LongTerminalPreparedChainProbability

@[expose] public section
/-! The structural core already chooses a correction, terminal reserve and
    concrete matching. Add the boundary preparation on that exact choice,
    without invoking a separate level-chain selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

def LongConcreteMatchedClassAtReserve
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (ξClass Δ:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))):Prop :=
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Q.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C S M Del

theorem long_core_reserve_boundary_prepared_event
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ) (gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM:ℝ)
    (BO:Fin K→ℝ) (ξSeed ΔSeed ζret ζselect terr τerr:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hPrepared:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)→
      ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hBoundary:FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1))
    (hReserve:LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀):
    LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
      θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
      (fun z D₀ C=>LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C ∧
        LongConcreteMatchedClassAtReserve P π d r Dv mm β ε Q ξClass Δ z θ a γ eps βList F hF weight w D₀ C) :=by
  obtain ⟨D₀,hvalid,havoid,C,hF₀,hcard,hrows,hhubs,hnew,horiginal,hmatching,hconcrete,D₂,hD₂,hremoved,hremain,hdis⟩:=hReserve
  have hterm:longTerminalProtectedReserve P π d r z z.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
      gammaLoss sigmaLoss e₀ (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) D₀ C.edges:=by
    simpa only [longTerminalProtectedReserve,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse,id] using
      (show D₀.Valid _ _ _ _ _ _ ∧ C.edges.card≤e₀ ∧ Disjoint D₀.removed C.edges ∧ _ from
        ⟨hvalid,hcard,hdis,horiginal⟩)
  exact ⟨D₀,C.edges,hterm,hPrepared z hBoundary D₀ C.edges hmatching,hmatching,hconcrete⟩

theorem long_core_reserve_boundary_prepared_probability
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ) (gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM:ℝ)
    (BO:Fin K→ℝ) (ξSeed ΔSeed ζret ζselect terr τerr:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hPrepared:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)→
      ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Prior:MarkedExpandedActualOutcome (U:=U) π d→Prop) (b:ℝ):
    b≤μ.probability (fun z=>Prior z ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1) ∧
      LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
        gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀)→
    b≤μ.probability (fun z=>Prior z ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1) ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
        (fun z D₀ C=>LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
          K θ Dv a γ eps βList F hF weight w D₀ C ∧
          LongConcreteMatchedClassAtReserve P π d r Dv mm β ε Q ξClass Δ z θ a γ eps βList F hF weight w D₀ C)) :=by
  intro hprob
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1,hz.2.1,long_core_reserve_boundary_prepared_event P π d r Dv mm β ε Q L a₀ b₀ e₀ gammaLoss sigmaLoss extra ξClass Δ
    θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM BO ξSeed ΔSeed ζret ζselect terr τerr F hF weight w hPrepared z F₀ hz.2.1 hz.2.2⟩
end Oberwolfach
