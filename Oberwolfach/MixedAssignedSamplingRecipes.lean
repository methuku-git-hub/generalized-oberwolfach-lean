module

public import Oberwolfach.OrdinaryAssignedSamplingWitness
public import Oberwolfach.LongAssignedSamplingWitness

@[expose] public section
/-! Select the original ordinary or marked sampling recipe according to the
actual class label.  The underlying factor family is fixed throughout. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} {U:I→Type} [∀i,Fintype (U i)] {n:ℕ}

def mixedAssignedIntervalProbability (K m:ℕ) (θ:ℝ)
    (label:I→Option (Fin K)) (F:∀i,U i→SimpleGraph (Fin n))
    (hF:∀i w,(F i w).IsRegularOfDegree 2) (i:I):U i→Bool→ℝ:=
  match label i with
  | none => longAssignedIntervalProbability (F i) (hF i) K m θ
  | some _ => ordinaryAssignedMarkedProbability (F i) (hF i) K θ ((m:ℝ)+1)

def mixedAssignedSpokeProbability (K m:ℕ) (s θ:ℝ)
    (label:I→Option (Fin K)) (F:∀i,U i→SimpleGraph (Fin n))
    (hF:∀i w,(F i w).IsRegularOfDegree 2) (i:I):U i→Bool→ℝ:=
  match label i with
  | none => longAssignedSpokeProbability (F i) (hF i) K m θ
  | some j => ordinaryAssignedSpokeProbability (F i) (hF i) K j s θ ((m:ℝ)+1)
end Oberwolfach
