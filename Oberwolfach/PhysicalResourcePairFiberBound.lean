module

public import Oberwolfach.PhysicalResourcePairAggregation

@[expose] public section
/-! A bounded-size physical fiber converts typed pair estimates into
physical codegree estimates, including collisions of different rim types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physical_resource_pair_weight_bounded_fibers
    {A B C:Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq B]
    (φ:A→B) (R:C→Finset A) (w:C→ℝ) (hw:∀c,0≤w c)
    (M:ℕ) (hM:∀x,(Finset.univ.filter (fun a=>φ a=x)).card≤M)
    (K:ℝ) (hK:0≤K) (hpair:∀a b,resourceOmittedPairWeight R w a b≤K)
    (x y:B) (hxy:x≠y):
    (∑c,if x∈(R c).image φ ∧ y∈(R c).image φ then w c else 0)≤(M:ℝ)^2*K := by
  let X:=Finset.univ.filter (fun a=>φ a=x)
  let Y:=Finset.univ.filter (fun a=>φ a=y)
  have hX:(X.card:ℝ)≤M:=by exact_mod_cast hM x
  have hY:(Y.card:ℝ)≤M:=by exact_mod_cast hM y
  have hX0:0≤(X.card:ℝ):=by positivity
  have hM0:0≤(M:ℝ):=by positivity
  calc
    _ ≤ ∑a∈X,∑b∈Y,resourceOmittedPairWeight R w a b :=
      physical_resource_pair_weight_le_fibers φ R w hw x y hxy
    _ ≤ ∑_a∈X,∑_b∈Y,K := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sum_le_sum (fun b _=>hpair a b)
    _ = (X.card:ℝ)*(Y.card:ℝ)*K := by simp [mul_assoc]
    _ ≤ (M:ℝ)^2*K := by
      have hh: (X.card:ℝ)*(Y.card:ℝ)≤(M:ℝ)*(M:ℝ):=
        mul_le_mul hX hY (by positivity) hM0
      nlinarith
end Oberwolfach
