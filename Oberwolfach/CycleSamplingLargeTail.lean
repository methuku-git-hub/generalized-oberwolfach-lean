module

public import Oberwolfach.CycleIndependentSampling

@[expose] public section
/-! Upper tails for the number of independently sampled fixed cycle
identifiers in any fixed test family. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C:Type} [Fintype C] [DecidableEq C]

theorem independent_cycle_count_large_tail
    (p:C→ℝ) (hp:∀ c,0≤p c) (hp1:∀ c,p c≤1) (A:C→Prop)
    (t:ℝ) (hmean:0<∑ c,if A c then p c else 0)
    (ht:(∑ c,if A c then p c else 0)≤t):
    let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
    let mean:=∑ c,if A c then p c else 0
    μ.probability (fun σ=>t ≤ independentCycleCount A σ)≤(Real.exp 1*mean/t)^t := by
  let μ:=fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c)
  let X:=fun c b=>if A c ∧ b=true then (1:ℝ) else 0
  have hX:∀ c b,X c b∈Set.Icc (0:ℝ) 1:=by
    intro c b;dsimp [X];split_ifs <;> norm_num
  have hE:(FiniteLaw.pi μ).expectation (fun σ=>∑ c,X c (σ c))=
    ∑ c,if A c then p c else 0:=independent_cycle_count_expectation p hp hp1 A
  have hh:=finiteLaw_independent_chernoff_large μ X hX (t:=t) (by rw [hE];exact hmean)
    (by rw [hE];exact ht)
  rw [hE] at hh
  exact hh
end Oberwolfach
