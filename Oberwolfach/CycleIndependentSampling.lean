module

public import Oberwolfach.FiniteChernoff
public import Oberwolfach.EdgeRetention

@[expose] public section
/-! Cycle identifiers are retained independently with the supplied,
possibly unequal probabilities. A fixed set of identifiers can encode
cycles through one vertex or through a pair of vertices. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C:Type} [Fintype C] [DecidableEq C]

def independentCycleCount (A:C→Prop) (σ:C→Bool):ℝ :=
  ∑ c,if A c ∧ σ c=true then 1 else 0

theorem independent_cycle_count_expectation
    (p:C→ℝ) (hp:∀ c,0≤p c) (hp1:∀ c,p c≤1) (A:C→Prop):
    (FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))).expectation
      (independentCycleCount A)=∑ c,if A c then p c else 0 := by
  let μ:=fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c)
  let X:=fun c b=>if A c ∧ b=true then (1:ℝ) else 0
  change (FiniteLaw.pi μ).expectation (fun σ=>∑ c,X c (σ c))=_
  rw [finiteLaw_pi_expectation_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h:A c <;> simp [μ,X,FiniteLaw.expectation,FiniteLaw.retentionCoin,Fintype.sum_bool,h]

theorem independent_cycle_count_chernoff
    (p:C→ℝ) (hp:∀ c,0≤p c) (hp1:∀ c,p c≤1) (A:C→Prop)
    (ε:ℝ) (he:0≤ε) (he1:ε≤1):
    let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
    let mean:=∑ c,if A c then p c else 0
    μ.probability (fun σ=>ε*mean≤|independentCycleCount A σ-mean|)≤
      2*Real.exp (-ε^2*mean/3) := by
  let μ:=fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c)
  let X:=fun c b=>if A c ∧ b=true then (1:ℝ) else 0
  have hX:∀ c b,X c b∈Set.Icc (0:ℝ) 1:=by
    intro c b;dsimp [X];split_ifs <;> norm_num
  have h:=finiteLaw_independent_chernoff μ X hX he he1
  change (FiniteLaw.pi μ).probability (fun σ=>ε*((FiniteLaw.pi μ).expectation
    (independentCycleCount A))≤|independentCycleCount A σ-(FiniteLaw.pi μ).expectation
      (independentCycleCount A)|)≤
    2*Real.exp (-ε^2*((FiniteLaw.pi μ).expectation (independentCycleCount A))/3) at h
  rw [independent_cycle_count_expectation] at h
  exact h
end Oberwolfach
