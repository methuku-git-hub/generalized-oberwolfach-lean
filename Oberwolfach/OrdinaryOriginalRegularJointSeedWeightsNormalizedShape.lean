module

public import Oberwolfach.OrdinaryEligibleHostJointWeightsBeforeTau
public import Oberwolfach.OrdinaryRegularTriangleMatchingHostInputs

@[expose] public section
/-! The original regular host supplies both retained ordinary-cycle weights
and the successor-sequence seed weights needed by the matching construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryOriginalRegularJointSeedWeightsNormalizedShape
    (K k:ℕ) (θhost α θ:ℝ) (hα:0<α) (hθ:0<θ)
    (hθhost:1/2≤θhost) (hratio:successorCycleRatio k+α/2≤1/2+α):Prop :=
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ ∀τ:ℝ,0<τ→∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℕ),
    P.IsRegularOfDegree D→(θhost+α)*n≤D→
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin ((k+2)*2)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) ∧
      (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed 
end Oberwolfach
