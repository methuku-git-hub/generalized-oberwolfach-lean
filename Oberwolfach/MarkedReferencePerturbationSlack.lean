module

public import Mathlib.Tactic

@[expose] public section

/-! Choose a single positive physical-change allowance from fixed lower
density bounds, leaving space between the sampled and target margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_reference_perturbation_slack
    (h:ℕ) (κ α ω plo klo:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hp:0<plo) (hk:0<klo):
    ∃ ζ:ℝ,0<ζ ∧
      κ/8+ζ≤κ/4 ∧ κ/8+(h:ℝ)*(2*ζ)≤κ/4 ∧
      κ/8+(h:ℝ)*ζ≤κ/4 ∧ κ/8+4*ζ≤κ/4 ∧
      ζ≤κ*ω/8 ∧
      (∀ p k:ℝ,plo≤p→klo≤k→
        2*ζ≤(3/2)*(α/8-α/16)*p^2 ∧
        ζ≤(α/8-α/16)*min p k/4) ∧
      (∀ N U:ℝ,0≤N→ω*N≤U→(κ/8)*U+ζ*N≤(κ/4)*U) := by
  let ζ:=min (κ/(128*((h:ℝ)+1)))
    (min (κ*ω/16) (min (α*plo^2/1024) (α*min plo klo/1024)))
  have hζ:0<ζ := by dsimp [ζ];positivity
  have hζ1:ζ≤κ/(128*((h:ℝ)+1)):=min_le_left _ _
  have hζ2:ζ≤κ*ω/16:=(min_le_right _ _).trans (min_le_left _ _)
  have hζ3:ζ≤α*plo^2/1024:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hζ4:ζ≤α*min plo klo/1024:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh:(0:ℝ)≤h:=Nat.cast_nonneg _
  have hbound:128*((h:ℝ)+1)*ζ≤κ := by
    have hd:0<128*((h:ℝ)+1):=by positivity
    have hq:ζ*(128*((h:ℝ)+1))≤κ := (le_div_iff₀ hd).mp hζ1
    nlinarith
  refine ⟨ζ,hζ,by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith,?_,?_⟩
  · intro p k hp' hk'
    have hp0:0<p:=lt_of_lt_of_le hp hp'
    have hk0:0<k:=lt_of_lt_of_le hk hk'
    have hsquare:plo^2≤p^2:=by nlinarith
    have hprod:=mul_le_mul_of_nonneg_left hsquare hα.le
    have hm:min plo klo≤min p k:=min_le_min hp' hk'
    have hmin:=mul_le_mul_of_nonneg_left hm hα.le
    constructor <;> nlinarith
  · intro N U hN hU
    have hprod:=mul_le_mul_of_nonneg_right hζ2 hN
    have hu:=mul_le_mul_of_nonneg_left hU (show 0≤κ/16 by positivity)
    nlinarith
end Oberwolfach
