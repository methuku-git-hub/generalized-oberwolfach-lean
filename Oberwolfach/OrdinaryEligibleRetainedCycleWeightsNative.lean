module

public import Oberwolfach.OrdinaryEligibleRetainedCycleWeights
public import Oberwolfach.OrdinaryCycleSumInstance

@[expose] public section
/-! Retained cycle weights in the native finite enumeration used by the
matching core; no dummy-length threshold is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_eligible_retained_cycle_weights_native
    (K:ℕ) (θhost α θ:ℝ) (hα:0<α) (hθ:0<θ):
    ∃B:Fin K→ℝ,(∀i,0<B i) ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),
    (∀v,(θhost+α)*n≤(P.degree v:ℝ))→
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤B i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) ∧
      (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) :=by
  obtain ⟨B,hB,hW⟩:=ordinary_eligible_retained_cycle_weights K θhost α θ hα hθ
  refine ⟨B,hB,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hW d
  refine ⟨N,?_⟩
  intro n hn hn0 U _ F hF hK Allowed hAllowed hthreshold P π hmin
  obtain ⟨w,hw,he,hzero⟩:=hN n hn hn0 U F hF hK Allowed hAllowed hthreshold P π hmin
  refine ⟨w,hw,?_,hzero⟩
  intro i hi x y
  have hsum:=ordinary_cycle_edge_sum_fin_decidable n (longPaddedSeedExponent i+2) (ordinaryEligibleHost P π d) (w i) x y
  exact hsum.symm.trans (he i hi x y)
end Oberwolfach
