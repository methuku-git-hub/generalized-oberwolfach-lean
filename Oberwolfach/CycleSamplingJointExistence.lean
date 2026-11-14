module

public import Oberwolfach.CycleSamplingJointEvent
public import Oberwolfach.CycleSamplingZeroMean

@[expose] public section
/-! A positive-probability outcome satisfies all fixed tests. Zero-mean
tests are handled on the support of the same original sampling law. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C J K:Type} [Fintype C] [DecidableEq C]

theorem independent_cycle_sampling_joint_exists
    (p:C→ℝ) (hp:∀ c,0≤p c) (hp1:∀ c,p c≤1)
    (T:Finset J) (A:J→C→Prop) (ε:J→ℝ) (he:∀ j∈T,0≤ε j)
    (he1:∀ j∈T,ε j≤1) (S:Finset K) (B:K→C→Prop) (t:K→ℝ)
    (hmean:∀ j∈S,0<∑ c,if B j c then p c else 0)
    (ht:∀ j∈S,(∑ c,if B j c then p c else 0)≤t j)
    (hsmall:(∑ j∈T,2*Real.exp (-(ε j)^2*(∑ c,if A j c then p c else 0)/3))+
      (∑ j∈S,(Real.exp 1*(∑ c,if B j c then p c else 0)/t j)^t j)<1):
    let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
    ∃ σ:C→Bool,0<μ.mass σ ∧
      (∀ j∈T,|independentCycleCount (A j) σ-(∑ c,if A j c then p c else 0)|<
        ε j*(∑ c,if A j c then p c else 0)) ∧
      (∀ j∈S,independentCycleCount (B j) σ<t j) ∧
      (∀ j,(∑ c,if B j c then p c else 0)=0→independentCycleCount (B j) σ=0) := by
  let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
  let good:=fun σ=>
    (∀ j∈T,|independentCycleCount (A j) σ-(∑ c,if A j c then p c else 0)|<
      ε j*(∑ c,if A j c then p c else 0)) ∧
    (∀ j∈S,independentCycleCount (B j) σ<t j)
  have hprob:0<μ.probability good:=by
    have hh:=independent_cycle_sampling_joint_event p hp hp1 T A ε he he1 S B t hmean ht
    dsimp only at hh
    linarith
  have hnon (σ:C→Bool) (_:σ∈Finset.univ):0 ≤ if good σ then μ.mass σ else 0:=by
    split_ifs;exact μ.nonneg σ;exact le_rfl
  have heq:μ.probability good=∑ σ,if good σ then μ.mass σ else 0:=by
    unfold FiniteLaw.probability
    apply Finset.sum_congr rfl
    intro σ _
    exact (ite_eq_ite (good σ) (μ.mass σ) 0).mpr trivial
  rw [heq] at hprob
  obtain ⟨σ,_,hσ⟩:=(Finset.sum_pos_iff_of_nonneg hnon).mp hprob
  split_ifs at hσ with hgood
  · refine ⟨σ,hσ,hgood.1,hgood.2,?_⟩
    intro j hz
    exact independent_cycle_count_zero_mean p hp hp1 (B j) hz σ hσ
  · exact (lt_irrefl _ hσ).elim
end Oberwolfach
