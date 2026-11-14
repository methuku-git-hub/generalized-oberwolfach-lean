module

public import Oberwolfach.LongReservedListConcentrationMargins

@[expose] public section
/-! Select list and deletion budgets, and their host threshold, uniformly
before the concrete capped vortex error and reference length are supplied. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_list_uniform_numeric_budgets
    (αHost ρ₀:ℝ) (hα:0<αHost) (hρ:0<ρ₀) (d:ℕ) (ζcap:ℝ) (hζcap:0<ζcap):
    let β:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
    ∃lam η ζ:ℝ,0<lam ∧ 0<η ∧ 0<ζ ∧ ζ≤ζcap ∧
    ∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lam+2*ζ)*n≤β*n ∧ (n:ℝ)^(3/4:ℝ)≤η*n ∧
      ∀(m:ℕ) (εQ:ℝ),εQ≤β/32→1/(100*(m:ℝ))≤β/16→
        β/2+εQ+1/(100*(m:ℝ))+η≤lam := by
  intro β
  have hβ:0<β:=by dsimp [β];positivity
  let lam:ℝ:=3*β/4
  let η:ℝ:=β/32
  let ζ:ℝ:=min ζcap (β/16)
  have hlam:0<lam:=by dsimp [lam];positivity
  have hη:0<η:=by dsimp [η];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζcap':ζ≤ζcap:=min_le_left _ _
  have hζbound:ζ≤β/16:=min_le_right _ _
  obtain ⟨N₁,hN₁⟩:=long_reserved_list_concentration_margins αHost ρ₀ hα hρ d
  obtain ⟨N₂,hN₂⟩:=eventually_three_quarters_and_constant_le_linear η 0 hη
  refine ⟨lam,η,ζ,hlam,hη,hζ,hζcap',max N₁ N₂,?_⟩
  intro n hn
  obtain ⟨herror,hmargin⟩:=hN₁ n (by omega)
  have hsub:(n:ℝ)^(3/4:ℝ)≤η*n:=by simpa using hN₂ n (by omega)
  have hbudget:lam+2*ζ≤β:=by dsimp [lam];linarith
  refine ⟨herror,by simpa only [β] using hmargin,
    mul_le_mul_of_nonneg_right hbudget (by positivity),hsub,?_⟩
  intro m εQ hε hm
  dsimp [lam,η]
  linarith
end Oberwolfach
