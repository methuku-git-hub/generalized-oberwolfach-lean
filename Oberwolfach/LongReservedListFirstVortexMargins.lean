module

public import Oberwolfach.LongSelectedListFirstVortexMargins

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_list_first_vortex_margins
    (γ pstar:ℝ) (hγ:0<γ) (hp:0<pstar):
    ∃β:ℝ,0<β ∧ β≤1 ∧ ∃dMin:ℕ,∀(ε δ lamMax ζMax:ℝ),0<ε→0<δ→0<lamMax→0<ζMax→
    ∃lam ζ:ℝ,0<lam ∧ lam≤1/100 ∧ lam≤lamMax ∧ lam≤δ*ε/32 ∧ 0<ζ ∧ ζ≤ζMax ∧ ζ≤lam/3 ∧
    ∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*(1/100:ℝ) ∧
      (lam+2*ζ)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n:=by
  exact long_selected_list_first_vortex_margins (1/100) γ pstar (by norm_num) hγ hp
end Oberwolfach
