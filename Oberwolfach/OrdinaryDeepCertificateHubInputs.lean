module

public import Oberwolfach.OrdinaryParentCleanupMarginChoices

@[expose] public section
/-! Supply the local certificate with the very same hub-weight constants
and cleanup margins used by the selected common event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_certificate_hub_inputs
    (m:ℕ) (βfreq ρ₀ c C cBoundary cInitial:ℝ)
    (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hc:0<c) (hC:0<C) (hBoundary:0<cBoundary) (hInitial:0<cInitial):
    let pstar:=ρ₀*(βfreq/200)/2;
    ∃γ eParent hParent κ BHub:ℝ,
      0<γ ∧ 0<eParent ∧ 0<hParent ∧ γ≤eParent ∧
      eParent≤cBoundary ∧ hParent≤cBoundary ∧ eParent≤cInitial ∧ hParent≤cInitial ∧
      0<κ ∧ κ≤1 ∧ κ≤ρ₀/8 ∧ 0<c ∧ 0≤BHub ∧ BHub=4*C/pstar^(3*m+1) ∧
      0<pstar ∧ pstar≤1 :=by
  intro pstar
  have hp:0<pstar:=by dsimp [pstar]; positivity
  have hs:0<βfreq/200:=by positivity
  have hs1:βfreq/200≤1:=by linarith
  have hmul:ρ₀*(βfreq/200)≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hρ1 hs.le
    nlinarith
  have hp1:pstar≤1:=by dsimp [pstar]; linarith
  obtain ⟨γ,eParent,hParent,κ,hγ,he,hh,hγe,heB,hhB,heI,hhI,hκ,hκ1,hκρ⟩:=
    ordinary_parent_cleanup_margin_choices cBoundary cInitial ρ₀ hBoundary hInitial hρ
  refine ⟨γ,eParent,hParent,κ,4*C/pstar^(3*m+1),hγ,he,hh,hγe,heB,hhB,heI,hhI,hκ,hκ1,hκρ,hc,?_,rfl,hp,hp1⟩
  positivity
end Oberwolfach
