module

public import Oberwolfach.OrdinaryOriginalRegularJointSeedWeights
public import Oberwolfach.OrdinaryRegularTriangleMatchingHostInputs

@[expose] public section
/-! The original regular host supplies both retained ordinary-cycle weights
and the successor-sequence seed weights needed by the matching construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 100000) originalRegularMatchingSeedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_regular_matching_seed_weights
    (K k:ℕ) (θhost α θ τ:ℝ) (hα:0<α) (hθ:0<θ) (hτ:0<τ)
    (hθhost:1/2≤θhost) (hratio:successorCycleRatio k+α/2≤1/2+α):
    ∃BO:Fin K→ℝ,∃BM A:ℝ,(∀i,0<BO i) ∧ 0<BM ∧ 0<A ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℕ),
    P.IsRegularOfDegree D→(θhost+α)*n≤D→
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (((k+2)*2-1)+1)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        A BM seed :=by
  obtain ⟨BO,hBO,hmain⟩:=ordinary_original_regular_joint_seed_weights K k θhost α θ τ hα hθ hτ hθhost hratio
  have hconst:=successorWeightConstants_pos k (α/4) (by positivity)
  refine ⟨BO,successorWeightUpper k (α/4),successorWeightLower k (α/4),hBO,hconst.2,hconst.1,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hmain d
  refine ⟨N,?_⟩
  intro n hn hn0 U _ F hF hK Allowed hAllowed hthreshold P π D hreg hdegree
  obtain ⟨w,seed,hw,hseed⟩:=hN n hn hn0 U F hF hK Allowed hAllowed hthreshold P π D hreg hdegree
  have hLen:((k+2)*2-1)+1=(k+2)*2:=Nat.sub_add_cancel (by omega)
  rw [hLen]
  exact ⟨w,seed,hw,hseed⟩
end Oberwolfach
