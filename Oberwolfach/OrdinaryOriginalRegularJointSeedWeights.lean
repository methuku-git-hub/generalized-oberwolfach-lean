module

public import Oberwolfach.OrdinaryEligibleHostJointWeights
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
local instance (priority := 100000) originalRegularSeedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_regular_joint_seed_weights
    (K k:ℕ) (θhost α θ τ:ℝ) (hα:0<α) (hθ:0<θ) (hτ:0<τ)
    (hθhost:1/2≤θhost) (hratio:successorCycleRatio k+α/2≤1/2+α):
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℕ),
    P.IsRegularOfDegree D→(θhost+α)*n≤D→
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin ((k+2)*2)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed :=by
  obtain ⟨BO,hBO,δ,hδ,hmain⟩:=ordinary_eligible_host_joint_weights K k θhost (α/2) θ τ (by positivity) hθ hτ
  refine ⟨BO,hBO,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hmain d
  refine ⟨N,?_⟩
  intro n hn hn0 U _ F hF hK Allowed hAllowed hthreshold P π D hreg hdegree
  let v:Fin n:=⟨0,hn0⟩
  have hDn:D≤n:=by
    have hh:=Finset.card_le_univ (P.neighborFinset v)
    simpa [SimpleGraph.card_neighborFinset_eq_degree,hreg v] using hh
  have hnR:0≤(n:ℝ):=by positivity
  have hDr:(D:ℝ)≤n:=by exact_mod_cast hDn
  have hDlo:(n:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) hnR
    nlinarith only [hh,hdegree]
  have hnear:∀v,|(P.degree v:ℝ)-D|≤δ*n:=by
    intro v
    rw [hreg v]
    simp only [sub_self,abs_zero]
    positivity
  have hminC:∀v,(θhost+α/2)*n≤(P.degree v:ℝ):=by
    intro v
    rw [hreg v]
    have hh:=mul_le_mul_of_nonneg_right (show θhost+α/2≤θhost+α by linarith) hnR
    exact hh.trans hdegree
  have hminS:∀v,(successorCycleRatio k+α/2)*n≤(P.degree v:ℝ):=by
    intro v
    rw [hreg v]
    have hh:=mul_le_mul_of_nonneg_right (show successorCycleRatio k+α/2≤θhost+α by linarith) hnR
    exact hh.trans hdegree
  obtain ⟨w,seed,hw,he,hzero,hseed⟩:=hN n hn hn0 U F hF hK Allowed hAllowed hthreshold P π D
    hDlo (by nlinarith) hnear hminC hminS
  refine ⟨w,seed,hw,?_⟩
  have hαeq:α/2/2=α/4:=by ring
  rw [hαeq] at hseed
  exact hseed
end Oberwolfach
