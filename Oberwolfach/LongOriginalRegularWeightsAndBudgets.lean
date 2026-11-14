module

public import Oberwolfach.LongOriginalHostSeedBudgets

@[expose] public section
/-! The original regular host supplies both retained ordinary weights and
the long seed, together with the matching budget for sufficiently large n. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority:=100000) longOriginalFullBudgetsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_original_regular_weights_and_budgets
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃m:ℕ,7≤m ∧ L≤m ∧ Even (m+1) ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧ ∀(K d:ℕ),2≤d→∀θ:ℝ,0<θ→
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ ∀τ:ℝ,0<τ→∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n))
      (hF:∀u,(F u).IsRegularOfDegree 2) (hK:0<K) (Allowed:Set ℕ)
      (hSet:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℕ),
    P.IsRegularOfDegree D→(allowedThreshold Allowed+α)*(n:ℝ)≤D→
    ∃w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0) ∧
      (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
      SuccessorSequenceWeightConditions P π (3*d) D τ A BM seed ∧
      (∀v,|(P.degree v:ℝ)-D|≤(0:ℝ)*n) ∧
      (∀i:Fin K,6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+(0:ℝ)*n≤τ*D) ∧
      (∀i:Fin K,5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/(n:ℝ)≤τ):=by
  obtain ⟨m,hm,hL,heven,A,BM,hA,hBM,hchoose⟩:=long_original_regular_joint_weights L α hα
  refine ⟨m,hm,hL,heven,A,BM,hA,hBM,?_⟩
  intro K d hd θ hθ
  obtain ⟨BO,hBO,hchoose⟩:=hchoose K d hd θ hθ
  refine ⟨BO,hBO,?_⟩
  intro τ hτ
  obtain ⟨Nw,hNw,hweights⟩:=hchoose τ hτ
  obtain ⟨Nb,hNb,hbudget⟩:=long_original_host_seed_budgets K d BO hBO τ hτ
  refine ⟨max Nw Nb,by omega,?_⟩
  intro n hn U _ F hF hK Allowed hSet hValid hAllowed P π D hreg hdegree
  have hn0:0<n:=by omega
  obtain ⟨w,seed,hw,he,hzero,hseed⟩:=hweights n (by omega) hn0 U F hF hK Allowed hSet hValid hAllowed P π D hreg hdegree
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hSet hValid
  have hnnonneg:0≤(n:ℝ):=by positivity
  have hDlo:(n:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤allowedThreshold Allowed+α by linarith) hnnonneg
    nlinarith only [hh,hdegree]
  obtain ⟨hbudgetV,hbudgetE⟩:=hbudget n (by omega) D hDlo
  refine ⟨w,seed,hw,he,hzero,hseed,?_,hbudgetV,hbudgetE⟩
  intro v
  rw [hreg v]
  simp
end Oberwolfach
