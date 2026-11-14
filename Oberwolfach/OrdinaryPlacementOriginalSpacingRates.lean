module

public import Oberwolfach.OrdinaryAbundanceSpacingChoice
public import Oberwolfach.OrdinaryMatchingSelectedRequiredForced

@[expose] public section
/-! The spacing already chosen from the abundance construction gives enough
room for forced complement placement, including protected vertices. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem ordinary_placement_delta_from_target_rate
    (β cap:ℝ) (hβ:0<β) (hcap:0<cap):
    ∃δ:ℝ,0<δ ∧ δ≤(β/100)^2 ∧ 5*Real.sqrt δ≤cap :=by
  let δ:ℝ:=min ((β/100)^2) ((cap/10)^2)
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδβ:δ≤(β/100)^2:=min_le_left _ _
  have hδcap:δ≤(cap/10)^2:=min_le_right _ _
  have hs:=Real.sqrt_le_sqrt hδcap
  have hroot:Real.sqrt ((cap/10)^2)=cap/10:=by rw [Real.sqrt_sq_eq_abs,abs_of_pos (by positivity : 0<cap/10)]
  rw [hroot] at hs
  exact ⟨δ,hδ,hδβ,by linarith⟩

theorem ordinary_forced_placement_rates_from_abundance_spacing
    (m d:ℕ) (hd:0<d) (θ δ α:ℝ)
    (hθ:0<θ) (hθsmall:θ≤1/100) (hδ:0<δ) (hθδ:θ≤δ/8) (hα:0<α)
    (hspace:1/(4*(d:ℝ))≤5*θ^2/256):
    ∃κ b z ζ matchErr:ℝ,0<κ ∧ 0<b ∧ 0<z ∧ 0<ζ ∧ 0<matchErr ∧
      b≤α/16 ∧ b≤δ/8 ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤(δ/8)/2 :=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hm1:0<(m:ℝ)+1:=by positivity
  have hm2:0<(m:ℝ)+2:=by positivity
  have hθ1:θ≤1:=by linarith
  have hθsq:θ^2≤θ/100:=by nlinarith
  have hinv0:0≤1/(d:ℝ):=by positivity
  have hinv:1/(d:ℝ)≤5*θ^2/64:=by
    have heq:1/(d:ℝ)=4*(1/(4*(d:ℝ))):=by field_simp
    rw [heq]
    nlinarith [hspace]
  let κ:ℝ:=min (θ/1024) (δ/(16*((m:ℝ)+2)))
  let b:ℝ:=min (α*θ/4096) (δ/16)
  let z:ℝ:=θ/1024
  let ζ:ℝ:=δ/(128*((m:ℝ)+1)*(d:ℝ))
  let matchErr:ℝ:=δ/128
  have hκ:0<κ:=by dsimp [κ];positivity
  have hb:0<b:=by dsimp [b];positivity
  have hz:0<z:=by dsimp [z];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have he:0<matchErr:=by dsimp [matchErr];positivity
  have hκθ:κ≤θ/1024:=min_le_left _ _
  have hκδ:κ≤δ/(16*((m:ℝ)+2)):=min_le_right _ _
  have hbθ:b≤α*θ/4096:=min_le_left _ _
  have hbδ:b≤δ/16:=min_le_right _ _
  have hbdiv:b/α≤θ/4096:=by
    apply (div_le_iff₀ hα).2
    nlinarith [hbθ]
  have hκterm:((m:ℝ)+2)*κ≤δ/16:=by
    have hh:=mul_le_mul_of_nonneg_left hκδ hm2.le
    have heq:((m:ℝ)+2)*(δ/(16*((m:ℝ)+2)))=δ/16:=by field_simp <;> ring
    rw [heq] at hh
    exact hh
  have hζterm:((m:ℝ)+1)*(d:ℝ)*ζ=δ/128:=by dsimp [ζ];field_simp <;> ring
  have hinv16:16/(d:ℝ)≤5*θ^2/4:=by
    have heq:16/(d:ℝ)=16*(1/(d:ℝ)):=by ring
    rw [heq]
    nlinarith [hinv]
  have hinv8:1/(8*(d:ℝ))≤5*θ^2/512:=by
    have heq:1/(8*(d:ℝ))=(1/(d:ℝ))/8:=by ring
    rw [heq]
    nlinarith [hinv]
  refine ⟨κ,b,z,ζ,matchErr,hκ,hb,hz,hζ,he,?_,?_,?_,?_,?_⟩
  · nlinarith [hbθ]
  · linarith
  · have hfirst:16/(d:ℝ)≤θ/80:=by linarith [hinv16,hθsq]
    have hsecond:16*κ≤θ/64:=by linarith [hκθ]
    have hthird:16*b/α≤θ/256:=by
      have heq:16*b/α=16*(b/α):=by ring
      rw [heq]
      linarith [hbdiv]
    dsimp [z]
    linarith [hfirst,hsecond,hthird]
  · nlinarith [hκterm]
  · rw [hζterm]
    dsimp [matchErr]
    nlinarith [hinv8,hθsq]
end Oberwolfach
