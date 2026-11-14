module

public import Oberwolfach.ConditionedColourMasks
public import Oberwolfach.EqualizedColourRetention

@[expose] public section

/-! Conditioning that forces the tested colour to be absent, and explicit
bounds when the original colour is uniform on a list. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_conditionEvent_true {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    μ.conditionEvent (fun _=>True)=μ := by
  apply finiteLaw_ext
  intro x
  have h := finiteLaw_conditionEvent_weight μ (fun _=>True) x
  simpa only [finiteLaw_probability_true,one_mul,ite_true] using h

theorem finiteLaw_conditionEvent_congr {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A B : Ω → Prop) (h : ∀ x,A x ↔ B x) :
    μ.conditionEvent A=μ.conditionEvent B := by
  have he : A=B := funext (fun x=>propext (h x))
  rw [he]

theorem conditioned_absent_colourMask_l1 {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (A : C×Bool → Prop) (hA : 0<μ.probability A)
    (c : C) (habs : ∀ x,A x → x.1≠c) :
    ((μ.conditionEvent A).map (colourMask c)).l1Distance (μ.map (colourMask c))=
      2*μ.probability (fun x=>x.1=c) := by
  let ν := (μ.conditionEvent A).map (colourMask c)
  let ν₀ := μ.map (colourMask c)
  let p := μ.probability (fun x=>x.1=c)
  have hp : 0≤p := finiteLaw_probability_nonneg _ _
  have hs (t : Bool) : ν.mass (some t)=0 := by
    have h := finiteLaw_conditionEvent_map_weight μ A (colourMask c) (some t)
    have hz : μ.probability (fun x=>A x ∧ colourMask c x=some t)=0 := by
      unfold FiniteLaw.probability
      apply Finset.sum_eq_zero
      intro x _
      have hn : ¬(A x ∧ colourMask c x=some t) := by
        rintro ⟨hx,hc⟩
        exact habs x hx ((colourMask_eq_some c x t).mp hc).1
      simp only [hn,ite_false]
    rw [hz] at h
    exact (mul_eq_zero.mp h).resolve_left hA.ne'
  have hn : ν.mass none=1 := by
    have h := ν.total
    rw [Fintype.sum_option,Fintype.sum_bool,hs true,hs false] at h
    linarith
  have hn₀ : ν₀.mass none=1-p := colourMask_mass_none μ c
  have hs₀ : ν₀.mass (some true)+ν₀.mass (some false)=p := colourMask_some_sum μ c
  change ν.l1Distance ν₀=2*p
  unfold FiniteLaw.l1Distance
  rw [Fintype.sum_option,Fintype.sum_bool,hn,hn₀,hs true,hs false]
  simp only [sub_sub_cancel,abs_of_nonneg hp,zero_sub,abs_neg,
    abs_of_nonneg (ν₀.nonneg (some true)),abs_of_nonneg (ν₀.nonneg (some false))]
  linarith

theorem uniformOn_withCoin_colour_le {C : Type*} [Fintype C]
    (L : Finset C) (hL : L.Nonempty) (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1)
    {l : ℕ} (hcard : L.card=l) (c : C) :
    ((FiniteLaw.uniformOn L hL).withCoin a ha).probability (fun x=>x.1=c)≤1/(l : ℝ) := by
  rw [finiteLaw_withCoin_colour]
  by_cases hc : c∈L
  · simp [FiniteLaw.uniformOn,hc,hcard]
  · simp only [FiniteLaw.uniformOn,hc,ite_false]
    positivity

theorem uniformOn_conditioned_colourMask_l1
    {C : Type*} [Fintype C] (L : Finset C) (hL : L.Nonempty)
    (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1)
    {l : ℕ} (hl : 1<l) (hcard : L.card=l) (b c : C) (hcb : c≠b) :
    let μ := (FiniteLaw.uniformOn L hL).withCoin a ha
    ((μ.conditionEvent (fun x=>x.1≠b)).map (colourMask c)).l1Distance (μ.map (colourMask c))≤
      if b∈L then 2/((l : ℝ)*((l : ℝ)-1)) else 0 := by
  classical
  dsimp only
  let μ := (FiniteLaw.uniformOn L hL).withCoin a ha
  have hlr : (1 : ℝ)<l := by exact_mod_cast hl
  have hl0 : (0 : ℝ)<l := by linarith
  have hpc := uniformOn_withCoin_colour_le L hL a ha hcard c
  have hqb : 0<1-μ.probability (fun x=>x.1=b) := by
    have hb := uniformOn_withCoin_colour_le L hL a ha hcard b
    have hlt : (1 : ℝ)/(l : ℝ)<1 := (div_lt_one hl0).mpr hlr
    linarith
  rw [conditioned_colourMask_l1 μ b c hcb hqb]
  have hpb : μ.probability (fun x=>x.1=b)=if b∈L then 1/(l : ℝ) else 0 := by
    rw [finiteLaw_withCoin_colour]
    simp only [FiniteLaw.uniformOn,hcard]
  rw [hpb]
  by_cases hb : b∈L
  · simp only [hb,ite_true]
    have hden : 0<1-1/(l : ℝ) := sub_pos.mpr ((div_lt_one hl0).mpr hlr)
    calc
      _ ≤ 2*(1/(l : ℝ))*(1/(l : ℝ))/(1-1/(l : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpc (by positivity)) hden.le
      _ = _ := by
        field_simp
  · simp only [hb,ite_false,mul_zero,zero_mul,zero_div]
    exact le_refl _

end Oberwolfach
