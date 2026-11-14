module

public import Oberwolfach.LongSelectedListMarginsOrdered

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_selected_list_first_vortex_margins
    (θ γ pstar:ℝ) (hθ:0<θ) (hγ:0<γ) (hp:0<pstar):
    ∃β:ℝ,0<β ∧ β≤1 ∧ ∃dMin:ℕ,∀(ε δ lamMax ζMax:ℝ),0<ε→0<δ→0<lamMax→0<ζMax→
    ∃lam ζ:ℝ,0<lam ∧ lam≤θ ∧ lam≤lamMax ∧ lam≤δ*ε/32 ∧ 0<ζ ∧ ζ≤ζMax ∧ ζ≤lam/3 ∧
    ∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*θ ∧
      (lam+2*ζ)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n:=by
  obtain ⟨β,hβ,hβ1,dMin,hList⟩:=long_selected_list_margins_ordered θ γ pstar hθ hγ hp
  refine ⟨β,hβ,hβ1,dMin,?_⟩
  intro ε δ lamMax ζMax hε hδ hmax hζmax
  let cap:=min lamMax (δ*ε/32)
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨lam,ζ,hlam,hlamθ,hlamcap,hζ,hζmax',hζlam,hbound⟩:=hList cap ζMax hcap hζmax
  exact ⟨lam,ζ,hlam,hlamθ,hlamcap.trans (min_le_left _ _),hlamcap.trans (min_le_right _ _),hζ,hζmax',hζlam,hbound⟩
end Oberwolfach
