module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! A single fixed lower bound applies to both the selected and approximate
spoke colours and to the two approximate rim probabilities. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem two_colour_uniform_seed_floor {U:Type} (s₀ pstar p₂ k₂:ℝ) (b:U→ℝ)
    (hs₀:0<s₀) (hpstar:0<pstar) (hp:pstar≤p₂) (hk:pstar≤k₂) (hb:∀ u,pstar≤b u):
    let floor:=min s₀ pstar
    let s:=fun (u:U) (j:Bool)=>if j then b u else s₀;
    0<floor ∧ floor≤p₂ ∧ floor≤k₂ ∧ ∀ u j,floor≤s u j:=by
  intro floor s
  have hf:0<floor:=lt_min hs₀ hpstar
  have hs:floor≤s₀:=min_le_left _ _
  have hp':floor≤pstar:=min_le_right _ _
  refine ⟨hf,hp'.trans hp,hp'.trans hk,?_⟩
  intro u j
  cases j <;> simp [s,hs,hp'.trans (hb u)]
end Oberwolfach
