module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget
public import Oberwolfach.OrdinaryPlacementOriginalSpacingRates

@[expose] public section
/-! Select the placement and physical-edit rates before the spacing. Only
retention, which naturally scales as the inverse spacing, is selected later. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem ordinary_placement_rates_before_spacing
    (m:ℕ) (θ δ α ζList:ℝ)
    (hθ:0<θ) (hθsmall:θ≤1/100) (hδ:0<δ) (hθδ:θ≤δ/8) (hα:0<α) (hζList:0<ζList):
    ∃κ b z matchErr σ:ℝ,0<κ ∧ 0<b ∧ 0<z ∧ 0<matchErr ∧ 0<σ ∧
      b≤ζList ∧ b≤α/16 ∧ b≤δ/8 ∧ z≤b/4 ∧
      (∀(n edit inner reserve conflict:ℝ),0≤n→
        edit≤σ*n→inner≤σ*n→ reserve≤σ*n→conflict≤σ*n→
        edit+2*inner+reserve+conflict≤b*n) ∧
    ∀(d:ℕ),0<d→1/(4*(d:ℝ))≤5*θ^2/256→
      ∃ζret:ℝ,0<ζret ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+matchErr≤(δ/8)/2 :=by
  let κ:ℝ:=min (θ/1024) (δ/(16*((m:ℝ)+2)))
  let b:ℝ:=min (min (α*θ/4096) (δ/16)) ζList
  let z:ℝ:=min (θ/1024) (b/8)
  let matchErr:ℝ:=δ/128
  have hκ:0<κ:=by dsimp [κ];positivity
  have hb:0<b:=by dsimp [b];positivity
  have hz:0<z:=by dsimp [z];positivity
  have he:0<matchErr:=by dsimp [matchErr];positivity
  have hκθ:κ≤θ/1024:=min_le_left _ _
  have hκδ:κ≤δ/(16*((m:ℝ)+2)):=min_le_right _ _
  have hbθ:b≤α*θ/4096:=(min_le_left _ _).trans (min_le_left _ _)
  have hbδ:b≤δ/16:=(min_le_left _ _).trans (min_le_right _ _)
  have hbList:b≤ζList:=min_le_right _ _
  have hzθ:z≤θ/1024:=min_le_left _ _
  have hzb:z≤b/8:=min_le_right _ _
  have hbdiv:b/α≤θ/4096:=by
    apply (div_le_iff₀ hα).2
    nlinarith [hbθ]
  have hm2:0<(m:ℝ)+2:=by positivity
  have hκterm:((m:ℝ)+2)*κ≤δ/16:=by
    have hh:=mul_le_mul_of_nonneg_left hκδ hm2.le
    have heq:((m:ℝ)+2)*(δ/(16*((m:ℝ)+2)))=δ/16:=by field_simp <;> ring
    rw [heq] at hh
    exact hh
  obtain ⟨σ,hσ,hσbudget⟩:=ordinary_matching_degree_rate_choice b hb
  refine ⟨κ,b,z,matchErr,σ,hκ,hb,hz,he,hσ,hbList,?_,?_,?_,hσbudget,?_⟩
  · nlinarith [hbθ]
  · linarith
  · linarith
  · intro d hd hspace
    have hdR:0<(d:ℝ):=by exact_mod_cast hd
    have hθsq:θ^2≤θ/100:=by nlinarith
    have hinv:1/(d:ℝ)≤5*θ^2/64:=by
      have heq:1/(d:ℝ)=4*(1/(4*(d:ℝ))):=by field_simp
      rw [heq]
      nlinarith [hspace]
    let ζret:ℝ:=δ/(128*((m:ℝ)+1)*(d:ℝ))
    have hζ:0<ζret:=by dsimp [ζret];positivity
    have hζterm:((m:ℝ)+1)*(d:ℝ)*ζret=δ/128:=by dsimp [ζret];field_simp <;> ring
    have hinv16:16/(d:ℝ)≤5*θ^2/4:=by
      have heq:16/(d:ℝ)=16*(1/(d:ℝ)):=by ring
      rw [heq]
      nlinarith [hinv]
    have hinv8:1/(8*(d:ℝ))≤5*θ^2/512:=by
      have heq:1/(8*(d:ℝ))=(1/(d:ℝ))/8:=by ring
      rw [heq]
      nlinarith [hinv]
    refine ⟨ζret,hζ,?_,?_,?_⟩
    · have hfirst:16/(d:ℝ)≤θ/80:=by linarith [hinv16,hθsq]
      have hsecond:16*κ≤θ/64:=by linarith [hκθ]
      have hthird:16*b/α≤θ/256:=by
        have heq:16*b/α=16*(b/α):=by ring
        rw [heq]
        linarith [hbdiv]
      linarith [hfirst,hsecond,hthird,hzθ]
    · nlinarith [hκterm]
    · rw [hζterm]
      dsimp [matchErr]
      nlinarith [hinv8,hθsq]
end Oberwolfach
