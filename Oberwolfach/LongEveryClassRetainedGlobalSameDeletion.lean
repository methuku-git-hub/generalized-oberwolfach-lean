module

public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingGlobal

@[expose] public section
/-! The retained-spoke packing and the orientation/matching witness use the
same selected class and the same physical deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_every_class_retained_global_same_deletion
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (γLoss σLoss ξClass:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hClass:LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξClass z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C)
    (hPrepared:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2):
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C S M Del ∧
        FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 := by
  apply long_every_class_same_deletion_ready Δ P π d r γLoss σLoss ξClass z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C hClass
    (fun S _=>FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2)
  intro S hSP hreg hedit hinner hreserve Del hDel
  exact hPrepared S hSP hreg hedit hinner hreserve
end Oberwolfach
