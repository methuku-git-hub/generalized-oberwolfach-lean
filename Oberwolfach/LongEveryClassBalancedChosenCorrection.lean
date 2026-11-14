module

public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.FirstVortexClassChosenCorrectionProof

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance everyClassChosenCorrectionFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_every_class_balanced_chosen_correction
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
    (hΔξ:Δ≤ξ)
    (hClass:LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξClass z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C)
    (hPrepared:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      FirstVortexClassPreparedOrientedOutcomeWithBalancedDegrees P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2):
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C S M Del ∧
        FirstVortexClassBalancedAtChosenCorrection P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 Del M :=by
  intro S hSP hreg hedit hinner hreserve
  obtain ⟨hpres,M,Del,hData⟩:=hClass S hSP hreg hedit hinner hreserve
  have hPrep:=hPrepared S hSP hreg hedit hinner hreserve
  refine ⟨hpres,M,Del,hData,?_⟩
  apply first_vortex_class_balanced_at_chosen_correction P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1 _ z.2 Del M Δ 0
    (by simpa using hData.2.2.2.2.2.1) (by simp) (by simpa using hΔξ) hData.1 hData.2.2.2.2.1 hData.2.1
  exact hPrep
end Oberwolfach
