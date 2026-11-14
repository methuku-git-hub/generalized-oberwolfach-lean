module

public import Oberwolfach.MarkedActiveHubDensityArithmetic

@[expose] public section
/-! A compatible choice for the two-step vortex error and active density.
The geometric constant is allowed to grow like C/ε. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_deep_ratio_parameter_choice
    (r:ℕ) (ρ ρ₀ t κ ξcap C:ℝ)
    (hρ:0<ρ) (hρ₀:0<ρ₀) (ht:0<t) (hκ:0<κ) (hξ:0<ξcap) (hC:0≤C):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ ε:ℝ,0<ε→ε≤ε₀→
      ∀ K:ℝ,0≤K→K≤C/ε→
      ∃ ω ξ:ℝ,0<ω ∧ 0<ξ ∧ ω≤ε/8 ∧ ω≤ρ₀*ε/64 ∧ ε^2≤ξ ∧ ξ≤ξcap ∧
        (4*K+(3*r+50:ℕ))*ξ≤κ/2 ∧ (1+2/ρ)*ξ≤t*ω/32:=by
  let a:=min (1/16:ℝ) (ρ₀/128)
  have ha:0<a:=by dsimp [a];positivity
  have ha1:a≤1/16:=min_le_left _ _
  have ha2:a≤ρ₀/128:=min_le_right _ _
  let B:=4*C+(3*r+50:ℕ)
  have hB:0<B:=by dsimp [B];positivity
  let D:=1+2/ρ
  have hD:0<D:=by dsimp [D];positivity
  let ε₀:=min 1 (min ξcap (min (κ/(4*B)) (t*a/(64*D))))
  have hε₀:0<ε₀:=by dsimp [ε₀];positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro ε he he₀ K hK hKC
  have he1:ε≤1:=he₀.trans (min_le_left _ _)
  have heξ:ε≤ξcap:=he₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heκ:ε≤κ/(4*B):=he₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have het:ε≤t*a/(64*D):=he₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heκ':ε*(4*B)≤κ:=(le_div_iff₀ (by positivity)).mp heκ
  have het':ε*(64*D)≤t*a:=(le_div_iff₀ (by positivity)).mp het
  have hKε:K*ε≤C:=(le_div_iff₀ he).mp hKC
  let ω:=a*ε
  let ξ:=ε^2
  have hω:0<ω:=by dsimp [ω];positivity
  have hxi:0<ξ:=by dsimp [ξ];positivity
  have hωv:ω≤ε/8:=by dsimp [ω];nlinarith [mul_le_mul_of_nonneg_right ha1 he.le]
  have hωu:ω≤ρ₀*ε/64:=by dsimp [ω];nlinarith [mul_le_mul_of_nonneg_right ha2 he.le]
  have hxicap:ξ≤ξcap:=by dsimp [ξ];nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)]
  have hscale:(4*K+(3*r+50:ℕ))*ξ≤κ/2:=by
    have hk1:=mul_le_mul_of_nonneg_right hKε he.le
    have he2:ε^2≤ε:=by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)]
    have hn:(0:ℝ)≤(3*r+50:ℕ):=by positivity
    have hh:=mul_le_mul_of_nonneg_left he2 hn
    dsimp [ξ,B] at *
    nlinarith [hk1,hh,heκ']
  have hgap:(1+2/ρ)*ξ≤t*ω/32:=by
    have hh:=mul_le_mul_of_nonneg_right het' he.le
    dsimp [D,ξ,ω] at *
    nlinarith [hh]
  exact ⟨ω,ξ,hω,hxi,hωv,hωu,le_rfl,hxicap,hscale,hgap⟩
end Oberwolfach
