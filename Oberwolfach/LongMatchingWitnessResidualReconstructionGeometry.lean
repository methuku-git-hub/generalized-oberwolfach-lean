module

public import Oberwolfach.LongDualResidualReconstructionGeometry
public import Oberwolfach.LongMatchingPhysicalCorrectionFields

@[expose] public section
/-! The reconstruction geometry follows from the actual same-sample
class-matching witness and its oriented residual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
local instance matchingReconstructionFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) matchingReconstructionSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_matching_witness_residual_reconstruction_geometry
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (K:ℕ) (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Small:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S M Del)
    (T:Finset {a:Fin n×Fin n // longEligibleResidualArc M Small ⊥ a}):
    let P:=longEligibleResidualArc M Small ⊥
    let E:=residualOrdinaryArc P T
    let K:=residualMarkedArc P T
    let tail:=fun e:E=>e.val.val.1
    let head:=fun e:E=>e.val.val.2
    let ktail:=fun e:K=>e.val.val.1
    let khead:=fun e:K=>π.symm e.val.val.2
    let Rrim:=markedPhysicalRimSet tail head ktail khead π;
    (∀e:E,tail e≠head e) ∧ (∀e:K,ktail e≠π (khead e)) ∧
    Function.Injective (markedPhysicalEdge tail head ktail khead π) ∧
    physicalEdgeGraph Rrim≤S ∧
    (∀x y,Small.Adj x y→({x,y}:Finset (Fin n))∉Rrim) :=by
  intro P E K' tail head ktail khead Rrim
  have hmatch:=long_matching_physical_correction_fields Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S Del M hw
  exact long_dual_residual_reconstruction_geometry S Small M hmatch.1 π T
end Oberwolfach
