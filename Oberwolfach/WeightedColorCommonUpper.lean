module

public import Oberwolfach.WeightedColorUpperTails

@[expose] public section

/-! One independent edge-colouring outcome satisfies all fixed upper tests.
The tests may be degrees, codegrees or supplied edge-weight functions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E C J : Type*} [Fintype E] [Fintype C] [Fintype J]
    [DecidableEq E] [Nonempty C]

theorem weightedColor_exponential_tail_mean (w : E → ℝ) (b : ℝ) (hb : 0<b)
    (hw : ∀ e,0≤w e ∧ w e≤b) (c : C) (U s t : ℝ) (hs : 0≤s)
    (hmean : (∑ e,w e)/Fintype.card C≤U) :
    (FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)).probability
      (fun σ=>t≤∑ e,if σ e=c then w e else 0)≤
      Real.exp ((U*(Real.exp s-1)-s*t)/b) := by
  refine (weightedColor_exponential_tail w b hb hw c s t hs).trans ?_
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hb.le
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_right hmean (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hs))) _

theorem weightedColor_common_upper (w : J → E → ℝ) (b U s t : J → ℝ)
    (hb : ∀ j,0<b j) (hw : ∀ j e,0≤w j e ∧ w j e≤b j)
    (hs : ∀ j,0≤s j) (hmean : ∀ j,(∑ e,w j e)/Fintype.card C≤U j)
    (hsmall : (∑ j : J,∑ _c : C,Real.exp ((U j*(Real.exp (s j)-1)-s j*t j)/b j))<1) :
    ∃ σ : E → C,∀ j c,(∑ e,if σ e=c then w j e else 0)<t j := by
  let μ := FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)
  let A : J×C → (E → C) → Prop := fun jc σ=>t jc.1≤∑ e,if σ e=jc.2 then w jc.1 e else 0
  let p : J×C → ℝ := fun jc=>Real.exp ((U jc.1*(Real.exp (s jc.1)-1)-s jc.1*t jc.1)/b jc.1)
  have hp : (∑ jc,p jc)<1 := by simpa only [p,Fintype.sum_prod_type] using hsmall
  obtain ⟨σ,_hσ,hgood⟩ := finiteLaw_common_event_exists μ Finset.univ A p
    (by
      intro jc _
      exact weightedColor_exponential_tail_mean (w jc.1) (b jc.1) (hb jc.1) (hw jc.1)
        jc.2 (U jc.1) (s jc.1) (t jc.1) (hs jc.1) (hmean jc.1)) hp
  exact ⟨σ,fun j c=>lt_of_not_ge (hgood (j,c) (Finset.mem_univ _))⟩

end Oberwolfach
