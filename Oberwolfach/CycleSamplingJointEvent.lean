module

public import Oberwolfach.CycleSamplingCommonEvent
public import Oberwolfach.CycleSamplingLargeTail
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! One independent sample simultaneously satisfies fixed relative-error
and upper-tail tests, without an independence assumption between tests. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C J K:Type} [Fintype C] [DecidableEq C]

theorem independent_cycle_sampling_joint_event
    (p:C→ℝ) (hp:∀ c,0≤p c) (hp1:∀ c,p c≤1)
    (T:Finset J) (A:J→C→Prop) (ε:J→ℝ) (he:∀ j∈T,0≤ε j)
    (he1:∀ j∈T,ε j≤1) (S:Finset K) (B:K→C→Prop) (t:K→ℝ)
    (hmean:∀ j∈S,0<∑ c,if B j c then p c else 0)
    (ht:∀ j∈S,(∑ c,if B j c then p c else 0)≤t j):
    let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
    let mA:=fun j=>∑ c,if A j c then p c else 0
    let mB:=fun j=>∑ c,if B j c then p c else 0
    1-(∑ j∈T,2*Real.exp (-(ε j)^2*mA j/3))-
      (∑ j∈S,(Real.exp 1*mB j/t j)^t j)≤
      μ.probability (fun σ=>(∀ j∈T,|independentCycleCount (A j) σ-mA j|<ε j*mA j) ∧
        (∀ j∈S,independentCycleCount (B j) σ<t j)) := by
  let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
  let mA:=fun j=>∑ c,if A j c then p c else 0
  let mB:=fun j=>∑ c,if B j c then p c else 0
  let EA:=fun σ=>∀ j∈T,|independentCycleCount (A j) σ-mA j|<ε j*mA j
  let EB:=fun σ=>∀ j∈S,independentCycleCount (B j) σ<t j
  let errA:=∑ j∈T,2*Real.exp (-(ε j)^2*mA j/3)
  let errB:=∑ j∈S,(Real.exp 1*mB j/t j)^t j
  have hA:1-errA≤μ.probability EA:=independent_cycle_sampling_common_event p hp hp1 T A ε he he1
  have hB:1-errB≤μ.probability EB:=by
    have hh:=finiteLaw_common_event_lower μ S (fun j σ=>t j ≤ independentCycleCount (B j) σ)
      (fun j=>(Real.exp 1*mB j/t j)^t j) (by
        intro j hj
        exact independent_cycle_count_large_tail p hp hp1 (B j) (t j) (hmean j hj) (ht j hj))
    simpa only [not_le] using hh
  exact (sub_le_sub_right hA errB).trans (finiteLaw_good_intersection μ EA EB errB hB)
end Oberwolfach
