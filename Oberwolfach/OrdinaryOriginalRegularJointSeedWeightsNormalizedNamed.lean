module

public import Oberwolfach.OrdinaryOriginalRegularJointSeedWeightsNormalizedShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_regular_joint_seed_weights_with_normalization
    (K k:ℕ) (θhost α θ:ℝ) (hα:0<α) (hθ:0<θ)
    (hθhost:1/2≤θhost) (hratio:successorCycleRatio k+α/2≤1/2+α):
    OrdinaryOriginalRegularJointSeedWeightsNormalizedShape K k θhost α θ hα hθ hθhost hratio :=by
  unfold OrdinaryOriginalRegularJointSeedWeightsNormalizedShape

  obtain ⟨BO,hBO,hmain⟩:=ordinary_eligible_host_joint_weights_before_tau K k θhost (α/2) θ (by positivity) hθ
  refine ⟨BO,hBO,?_⟩
  intro τ hτ
  obtain ⟨δ,hδ,hmain⟩:=hmain τ hτ
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
  refine ⟨w,seed,hw,he,hzero,?_⟩
  have hαeq:α/2/2=α/4:=by ring
  rw [hαeq] at hseed
  exact hseed
end Oberwolfach
