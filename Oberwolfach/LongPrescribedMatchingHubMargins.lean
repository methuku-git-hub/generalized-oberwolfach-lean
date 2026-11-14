module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_prescribed_matching_hub_margins
    (ρ₀:ℝ) (hρ₀:0<ρ₀):
    ∃b α:ℝ,0<b ∧ 0<α ∧ α/16≤b ∧
      (∀ρ:ℝ,ρ₀≤ρ→b≤(ρ/40000)/16) ∧
      ∃L:ℕ,1≤L ∧ ∀m:ℕ,L≤m→4/(m:ℝ)≤b/2:=by
  let b:ℝ:=ρ₀/1280000
  let α:ℝ:=b
  have hb:0<b:=by dsimp [b];positivity
  have hα:0<α:=hb
  have hαb:α/16≤b:=by dsimp [α];linarith
  obtain ⟨L,hL⟩:=exists_nat_gt (8/b)
  refine ⟨b,α,hb,hα,hαb,?_,max L 1,le_max_right _ _,?_⟩
  · intro ρ hρ
    dsimp [b]
    linarith
  · intro m hm
    have hLm:L≤m:=le_trans (le_max_left _ _) hm
    have hmpos:0<m:=by omega
    have hmR:(0:ℝ)<m:=by exact_mod_cast hmpos
    have hL':8/b<(m:ℝ):=lt_of_lt_of_le hL (by exact_mod_cast hLm)
    have hh:8<(m:ℝ)*b:=(div_lt_iff₀ hb).1 hL'
    apply (div_le_iff₀ hmR).2
    nlinarith only [hh]
end Oberwolfach
