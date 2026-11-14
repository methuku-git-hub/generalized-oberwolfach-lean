module

public import Oberwolfach.OrdinaryTriangleInitialDeepBalanceBeforeSpacing
public import Oberwolfach.OrdinaryInitialMatchingMarginsAt

@[expose] public section
/-! Named initial, matching and later balance selectors, with their boundary
coefficients chosen before the vortex and matching spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryTriangleInitialDeepBalanceSelector (ρ₀ α pmin hmin cBoundary:ℝ):Prop :=
    ∀ε:ℝ,0<ε→ε<1/4→∀ηProfile ζ:ℝ,0<ηProfile→0<ζ→
    ∃δDeep rate:ℝ,0<δDeep ∧ δDeep≤α ∧ 0<rate ∧
    ∀ηInitial:ℝ,0<ηInitial→∃δInitial:ℝ,0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance:ℕ,1≤mInitial ∧ 1≤mBalance ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance

def OrdinaryTriangleInitialMatchingMarginSelector (ρ₀ α pmin hmin cInitial:ℝ):Prop :=
    ∀ε:ℝ,0<ε→ε<1/4→∀bal:ℝ,0<bal→
    ∃δ η:ℝ,0<δ ∧ δ≤α ∧ δ≤bal ∧ 0<η ∧
    ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→∃m₀ N:ℕ,1≤m₀ ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cInitial δ η β d m₀ N

theorem ordinary_triangle_early_balance_selectors
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary cInitial:ℝ,0<cBoundary ∧ 0<cInitial ∧
      OrdinaryTriangleInitialDeepBalanceSelector ρ₀ α pmin hmin cBoundary ∧
      OrdinaryTriangleInitialMatchingMarginSelector ρ₀ α pmin hmin cInitial :=by
  obtain ⟨cBoundary,hcBoundary,hDeep⟩:=ordinary_triangle_initial_deep_balance_before_spacing ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
  obtain ⟨cInitial,hcInitial,hInitial⟩:=ordinary_initial_matching_edit_margins_named_before_spacing ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
  exact ⟨cBoundary,cInitial,hcBoundary,hcInitial,hDeep,hInitial⟩
end Oberwolfach
