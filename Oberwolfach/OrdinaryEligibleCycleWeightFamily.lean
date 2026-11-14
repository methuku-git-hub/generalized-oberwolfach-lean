module

public import Oberwolfach.OrdinaryEligibleCycleWeights

@[expose] public section
/-! A finite family of cycle lengths uses fixed eligible-host weights with
one common order threshold, chosen before the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) eligibleCycleFamilyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_eligible_cycle_weight_family
    (I:Type) [Fintype I] (length:I→ℕ) (hlen:∀i,3≤length i)
    (θ α:ℝ) (hα:0<α) (hthreshold:∀i,cycleThreshold (length i)≤θ):
    ∃c B:I→ℝ,(∀i,0<c i) ∧ (∀i,0<B i) ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),
    (∀v,(θ+α)*n≤(P.degree v:ℝ))→
    ∃w:∀i,OrdinaryCycle (ordinaryEligibleHost P π d) (length i)→ℝ,
      (∀i C,c i/(n:ℝ)^(length i-2)≤w i C ∧ w i C≤B i/(n:ℝ)^(length i-2)) ∧
      (∀i x y,(∑C,if C.val.val.Adj x y then w i C else 0)=
        if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) :=by
  choose c B hc hB hweight using fun i=>ordinary_eligible_cycle_weights (length i) (hlen i) α hα
  refine ⟨c,B,hc,hB,?_⟩
  intro d
  choose N hN using fun i=>hweight i d
  refine ⟨Finset.univ.sup N,?_⟩
  intro n hn P π hmin
  have hbound (i:I):N i≤n:=(Finset.le_sup (f:=N) (Finset.mem_univ i)).trans hn
  have hmin' (i:I):∀v,(cycleThreshold (length i)+α)*n≤(P.degree v:ℝ):=by
    intro v
    have hn0:0≤(n:ℝ):=by positivity
    have hh:cycleThreshold (length i)+α≤θ+α:=by linarith [hthreshold i]
    exact (mul_le_mul_of_nonneg_right hh hn0).trans (hmin v)
  choose w hw he using fun i=>hN i n (hbound i) P π (hmin' i)
  exact ⟨w,hw,he⟩
end Oberwolfach
