module

public import Oberwolfach.OrdinaryEligibleRetainedCycleWeightsNative
public import Oberwolfach.OrdinaryEligibleSuccessorWeights

@[expose] public section
/-! Choose both types of fixed wheel weights on the same physically eligible
host, before exposing the common sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_eligible_host_joint_weights_before_tau
    (K k:ℕ) (θhost α θ:ℝ) (hα:0<α) (hθ:0<θ):
    ∃B:Fin K→ℝ,(∀i,0<B i) ∧ ∀τ:ℝ,0<τ→∃δ:ℝ,0<δ ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℝ),
    (n:ℝ)/2≤D→D≤2*n→(∀v,|(P.degree v:ℝ)-D|≤δ*n)→
    (∀v,(θhost+α)*n≤(P.degree v:ℝ))→
    (∀v,(successorCycleRatio k+α)*n≤(P.degree v:ℝ))→
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃weight:(Fin ((k+2)*2)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤B i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) ∧
      (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        (successorWeightLower k (α/2)) (successorWeightUpper k (α/2)) weight :=by
  obtain ⟨B,hB,hC⟩:=ordinary_eligible_retained_cycle_weights_native K θhost α θ hα hθ
  refine ⟨B,hB,?_⟩
  intro τ hτ
  obtain ⟨δ,hδ,hS⟩:=ordinary_eligible_successor_weights k α τ hα hτ
  refine ⟨δ,hδ,?_⟩
  intro d
  obtain ⟨NC,hNC⟩:=hC d
  obtain ⟨NS,hNS⟩:=hS d
  refine ⟨max NC NS,?_⟩
  intro n hn hn0 U _ F hF hK Allowed hAllowed hthreshold P π D hDlo hDhi hnear hminC hminS
  obtain ⟨w,hw,he,hzero⟩:=hNC n (by omega) hn0 U F hF hK Allowed hAllowed hthreshold P π hminC
  obtain ⟨weight,hs⟩:=hNS n (by omega) P π D hDlo hDhi hnear hminS
  refine ⟨w,weight,hw,he,hzero,?_⟩
  convert hs using 1 <;> congr! 5
end Oberwolfach
