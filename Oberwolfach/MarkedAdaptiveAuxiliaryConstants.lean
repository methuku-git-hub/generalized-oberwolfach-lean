module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Auxiliary positive reference scales can be chosen from the original
index-density lower bound and the fixed wheel length. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_adaptive_auxiliary_constants
    (m:ℕ) (hm:1≤m) (ρ₀:ℝ) (hρ₀:0<ρ₀):
    ∃ω pstar kstar tstar:ℝ,
      0<ω ∧ 0<pstar ∧ 0<kstar ∧ 0<tstar ∧ tstar≤1/100 ∧ tstar≤1 ∧
      4*ω≤ρ₀ ∧ 4*(m:ℝ)*pstar≤ρ₀*(1/100) ∧ tstar≤(1/100)/(m:ℝ) ∧
      ∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2 := by
  have hm1:(1:ℝ)≤m:=by exact_mod_cast hm
  have hm0:0<(m:ℝ):=by positivity
  let ω:=ρ₀/8
  let pstar:=ρ₀/(800*(m:ℝ))
  let kstar:=ρ₀/(400*(m:ℝ))
  let tstar:=(1/100:ℝ)/(m:ℝ)
  have hω:0<ω:=by dsimp [ω];positivity
  have hp:0<pstar:=by dsimp [pstar];positivity
  have hk:0<kstar:=by dsimp [kstar];positivity
  have ht:0<tstar:=by dsimp [tstar];positivity
  have ht100:tstar≤1/100:=by
    dsimp [tstar]
    apply (div_le_iff₀ hm0).2
    nlinarith
  have hpbound:4*(m:ℝ)*pstar≤ρ₀*(1/100):=by
    dsimp [pstar]
    field_simp
    linarith
  refine ⟨ω,pstar,kstar,tstar,hω,hp,hk,ht,ht100,(by linarith),?_,hpbound,le_rfl,?_⟩
  · dsimp [ω];linarith
  · intro ρ hρ
    have hρpos:0<ρ:=hρ₀.trans_le hρ
    constructor
    · dsimp [kstar]
      apply (div_le_iff₀ (show 0<400*(m:ℝ) by positivity)).2
      nlinarith
    · dsimp [kstar]
      have hmne:(m:ℝ)≠0:=ne_of_gt hm0
      field_simp
      nlinarith
end Oberwolfach
