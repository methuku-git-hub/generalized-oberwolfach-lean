module

public import Oberwolfach.OrdinaryUnreservedPackingFromParent

@[expose] public section
/-! Choose one small deletion scale that simultaneously controls the
packing's cut, degree, configuration-count and weight-load losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_unreserved_packing_margin_choice (r:ℕ) (β₀ h B ε₀ εstar:ℝ)
    (hβ:0<β₀) (hh:0<h) (hB:0≤B) (hε:ε₀<εstar):
    ∃t:ℝ,0<t ∧ ∀ξ ζ:ℝ,0≤ξ→0≤ζ→ξ≤t→ζ≤t→
      h/2≤h-ξ-ζ ∧ β₀/2+ξ+ζ≤β₀ ∧ 8*(ξ+ζ)≤β₀-β₀/2 ∧
      5*(r:ℝ)^4*(ξ+ζ)≤β₀-β₀/2 ∧
      ε₀+8*(r:ℝ)^4*B*(ξ+ζ)≤εstar:=by
  let C:ℝ:=1+8+5*(r:ℝ)^4+8*(r:ℝ)^4*B
  have hC:0<C:=by dsimp [C];positivity
  have hC8:8≤C:=by
    dsimp [C]
    have h1:0≤5*(r:ℝ)^4:=by positivity
    have h2:0≤8*(r:ℝ)^4*B:=by positivity
    linarith
  have hCT:5*(r:ℝ)^4≤C:=by
    dsimp [C]
    have h2:0≤8*(r:ℝ)^4*B:=by positivity
    linarith
  have hCW:8*(r:ℝ)^4*B≤C:=by
    dsimp [C]
    have h1:0≤5*(r:ℝ)^4:=by positivity
    linarith
  let t:=min (β₀/(16*C)) (min (h/8) ((εstar-ε₀)/(8*C)))
  have ht:0<t:=by dsimp [t];positivity
  have htβ:t≤β₀/(16*C):=min_le_left _ _
  have hth:t≤h/8:=(min_le_right _ _).trans (min_le_left _ _)
  have htε:t≤(εstar-ε₀)/(8*C):=(min_le_right _ _).trans (min_le_right _ _)
  have hb:16*C*t≤β₀:=by
    have htβ' := (le_div_iff₀ (by positivity:0<16*C)).mp htβ
    nlinarith only [htβ']
  have he:8*C*t≤εstar-ε₀:=by
    have htε' := (le_div_iff₀ (by positivity:0<8*C)).mp htε
    nlinarith only [htε']
  refine ⟨t,ht,?_⟩
  intro ξ ζ hξ hζ hξt hζt
  have hsum:0≤ξ+ζ:=by linarith
  have hsumt:ξ+ζ≤2*t:=by linarith
  have hcut:h/2≤h-ξ-ζ:=by linarith
  have hC1:1≤C:=by linarith
  have hdeg:(ξ+ζ)≤C*(ξ+ζ):=by nlinarith
  have h8:8*(ξ+ζ)≤C*(ξ+ζ):=mul_le_mul_of_nonneg_right hC8 hsum
  have hT:5*(r:ℝ)^4*(ξ+ζ)≤C*(ξ+ζ):=mul_le_mul_of_nonneg_right hCT hsum
  have hW:8*(r:ℝ)^4*B*(ξ+ζ)≤C*(ξ+ζ):=mul_le_mul_of_nonneg_right hCW hsum
  have hcap:C*(ξ+ζ)≤2*C*t:=by nlinarith
  refine ⟨hcut,?_,?_,?_,?_⟩ <;> nlinarith only [hb,he,hdeg,h8,hT,hW,hcap,ht.le,hC.le]
end Oberwolfach
