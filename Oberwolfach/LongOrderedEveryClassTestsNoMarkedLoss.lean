module

public import Oberwolfach.LongOrderedEveryClassSampleTests

@[expose] public section
/-! Record the reserved-label concentration test alongside the earlier
ordered tests. This is the test already available in the parent event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

def LongOrderedEveryClassTestsNoMarkedLoss
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (r K d:ℕ)
    (θ ρ D:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (z:MarkedExpandedActualOutcome (U:=U) π d):Prop :=
    LongOrderedEveryClassSampleTests P π r K d θ ρ D F hF z ∧
    ∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1/100:ℝ)|<(n:ℝ)^(3/4:ℝ)
end Oberwolfach
