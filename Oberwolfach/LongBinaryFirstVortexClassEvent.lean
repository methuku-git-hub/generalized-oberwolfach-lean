module

public import Oberwolfach.LongBinaryFirstVortexPartitionInputs
public import Oberwolfach.LongSelectedFirstVortexClassSameDeletion

@[expose] public section
/-! The protected class selected for binary colour zero has exactly the
regular degree needed for the first-vortex packing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_binary_first_vortex_class_event
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm (Fin n)) (d Bpart:ℕ) (ξ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (hBinary:∀A:SimpleGraph (Fin n),(∀v,A.degree v≤Bpart)→
      ∃S:SimpleGraph (Fin n),S≤G ∧ S.IsRegularOfDegree (2*binaryClassMultiplicity D (Fintype.card U) 0) ∧
        (∀x y,(spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)⊔A).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)):
    ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤Bpart)→
      ∃S:SimpleGraph (Fin n),S≤G ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,(spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)⊔A).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n):=by
  simpa only [binaryClassMultiplicity,Matrix.cons_val_zero] using hBinary
end Oberwolfach
