module

public import Oberwolfach.OrdinaryEligibleCycleWeights
public import Oberwolfach.OrdinaryAssignedNonretainedZero

@[expose] public section
/-! Choose fractional cycle weights only for retained factor lengths. Dummy
padded lengths receive the zero function and require no host threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) retainedCycleFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_eligible_retained_cycle_weights
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
  choose c B hc hB hweight using fun i:Fin K=>ordinary_eligible_cycle_weights
    (longPaddedSeedExponent i+2) (by have hh:=long_padded_seed_exponent_positive i;omega) α hα
  refine ⟨B,hB,?_⟩
  intro d
  choose N hN using fun i=>hweight i d
  refine ⟨Finset.univ.sup N,?_⟩
  intro n hn hn0 U _ F hF hK Allowed hAllowed hthreshold P π hmin
  have hbound (i:Fin K):N i≤n:=(Finset.le_sup (f:=N) (Finset.mem_univ i)).trans hn
  have hex:∀i:Fin K,∃wi:OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
      (∀C,0≤wi C ∧ wi C≤B i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (i∈longRetainedSeedIndices F hF K θ→∀x y,(∑C,if C.val.val.Adj x y then wi C else 0)=
        if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) ∧
      (i∉longRetainedSeedIndices F hF K θ→∀C,wi C=0):=by
    intro i
    by_cases hi:i∈longRetainedSeedIndices F hF K θ
    · have ha:=long_retained_padded_length_allowed hn0 F hF Allowed hAllowed K hK θ hθ i hi
      have hmin':∀v,(cycleThreshold (longPaddedSeedExponent i+2)+α)*n≤(P.degree v:ℝ):=by
        intro v
        have hh:=hthreshold _ ha
        have hnR:0≤(n:ℝ):=by positivity
        exact (mul_le_mul_of_nonneg_right (by linarith : cycleThreshold (longPaddedSeedExponent i+2)+α≤θhost+α) hnR).trans (hmin v)
      obtain ⟨wi,hwi,he⟩:=hN i n (hbound i) P π hmin'
      refine ⟨wi,?_,fun _=>he,?_⟩
      · intro C
        have hh:=hwi C
        constructor
        · have hn0':0≤c i/(n:ℝ)^(longPaddedSeedExponent i):=by
            have hci:=hc i
            positivity
          have hl: c i/(n:ℝ)^(longPaddedSeedExponent i)≤wi C:=by
            simpa only [Nat.add_sub_cancel] using hh.1
          exact hn0'.trans hl
        · simpa only [Nat.add_sub_cancel] using hh.2
      · intro hnhi
        exact (hnhi hi).elim
    · refine ⟨fun _=>0,?_,?_,?_⟩
      · intro C
        constructor
        · rfl
        · exact div_nonneg (hB i).le (by positivity)
      · intro hh
        exact (hi hh).elim
      · intro _ C
        rfl
  choose w hw he hz using hex
  exact ⟨w,hw,he,hz⟩
end Oberwolfach
