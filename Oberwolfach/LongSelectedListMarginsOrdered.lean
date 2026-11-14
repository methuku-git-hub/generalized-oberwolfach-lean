module

public import Oberwolfach.LongSelectedListMargins

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem long_selected_list_margins_ordered
    (θ γ pstar:ℝ) (hθ:0<θ) (hγ:0<γ) (hp:0<pstar):
    ∃β:ℝ,0<β ∧ β≤1 ∧ ∃dMin:ℕ,∀(lamMax ζMax:ℝ),0<lamMax→0<ζMax→
    ∃lam ζ:ℝ,0<lam ∧ lam≤θ ∧ lam≤lamMax ∧ 0<ζ ∧ ζ≤ζMax ∧ ζ≤lam/3 ∧
    ∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*θ ∧
      (lam+2*ζ)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n:=by
  obtain ⟨β,lam₀,ζ,hβ,hβ1,hlam₀,hlamθ,hζ,dMin,hd⟩:=long_selected_list_margins θ γ pstar hθ hγ hp
  refine ⟨β,hβ,hβ1,dMin,?_⟩
  intro lamMax ζMax hMax hζMax
  let lam:=min lam₀ lamMax
  let ζ':=min ζ (min ζMax (lam/3))
  have hlam:0<lam:=lt_min hlam₀ hMax
  have hζ':0<ζ':=lt_min hζ (lt_min hζMax (by positivity))
  have hζle:ζ'≤ζ:=min_le_left _ _
  have hle:lam≤lam₀:=min_le_left _ _
  refine ⟨lam,ζ',hlam,hle.trans hlamθ,min_le_right _ _,hζ',(min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _),?_⟩
  intro d hdMin hd2
  obtain ⟨N,hN⟩:=hd d hdMin hd2
  refine ⟨N,?_⟩
  intro n hn
  obtain ⟨h1,h2,h3⟩:=hN n hn
  have hh:=mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg n)
  have hhζ:=mul_le_mul_of_nonneg_right hζle (Nat.cast_nonneg n)
  exact ⟨h1,h2,by nlinarith⟩
end Oberwolfach
