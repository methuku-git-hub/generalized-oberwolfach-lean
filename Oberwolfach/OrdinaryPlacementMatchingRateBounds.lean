module

public import Oberwolfach.OrdinaryPlacementStage

@[expose] public section
/-! Matching rates selected by the placement hierarchy at the actual cutoff. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryPlacementMatchingRateBounds
    (K:ℕ) (θ κ' b z δ matchErr lam a γ:ℝ):Prop :=
0<lam ∧ lam≤1 ∧ 0<a ∧ 0<γ ∧
      lam≤θ/10 ∧ γ≤lam/10 ∧ a≤κ' ∧ γ≤κ' ∧ a≤b/16 ∧ a≤z/16 ∧ γ≤z/16 ∧ γ≤θ ∧
      a≤θ/(1600*(K:ℝ)*(K:ℝ)) ∧
      0≤lam+γ*(1-θ+lam) ∧ lam+γ*(1-θ+lam)≤θ/8 ∧
      lam+γ*(1-θ+lam)≤matchErr ∧ lam+γ*(1-θ+lam)<θ ∧
      ∀n:ℕ,2*((max a γ)*n)≤δ*n/8

end Oberwolfach
