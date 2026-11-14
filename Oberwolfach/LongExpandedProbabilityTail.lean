module

public import Oberwolfach.LongAssignedJointFailureUniform

@[expose] public section
/-! Once the matching scales and weights are fixed, choose the order
threshold so their explicit error fits any earlier positive allowance. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_expanded_probability_tail_eventually_small
    (r K d:ℕ) (ni:Fin K→ℕ) (ρ₀ BM:ℝ) (BO:Fin K→ℝ) (t ξ η:ℝ)
    (hρ:0<ρ₀) (hBM:0<BM) (hBO:∀i,0<BO i) (ht:0<t) (hξ:0<ξ) (hη:0<η):
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2));
    ∃N:ℕ,∀n≥N,∀U:Type,[Fintype U]→Fintype.card U≤n→
      4*(Fintype.card U:ℝ)*Real.exp (-2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(n:ℝ)))+
        mixedSeedFailureBound (Fin n) U d (r+4) K (fun i=>ni i+1) BMseed BOseed t<η := by
  dsimp only
  have hp:0<min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1)))):=by positivity
  have hB:0<2*BM/(min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1)))))^(2*(r+4)+1):=by positivity
  have hO:∀i,0<2*BO i/(min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1)))))^(2*(ni i+2)):=by
    intro i
    have hi:=hBO i
    positivity
  exact eventually_assigned_seed_spoke_failure_below d (r+4) K (fun i=>ni i+1) _ _ t ξ η hB hO ht hξ hη
end Oberwolfach
