module

public import Oberwolfach.ColourMasks
public import Oberwolfach.FiniteLawL1

@[expose] public section

/-! The change in the distribution of one colour when a different colour
is excluded. All retention-coin probabilities remain unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_split {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.probability (fun x=>P x ∧ Q x)+μ.probability (fun x=>P x ∧ ¬Q x)=μ.probability P := by
  unfold FiniteLaw.probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp,hq]

theorem conditioned_colourMask_some_weight {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (b c : C) (hcb : c≠b) (t : Bool) :
    (1-μ.probability (fun x=>x.1=b))*
      ((μ.conditionEvent (fun x=>x.1≠b)).map (colourMask c)).mass (some t)=
        (μ.map (colourMask c)).mass (some t) := by
  have hq := finiteLaw_probability_compl μ (fun x=>x.1=b)
  have he : μ.probability (fun x=>x.1≠b)=1-μ.probability (fun x=>x.1=b) := by linarith
  rw [← he,finiteLaw_conditionEvent_map_weight,finiteLaw_map_mass_probability]
  apply finiteLaw_probability_congr
  intro x
  constructor
  · exact And.right
  · intro hx
    have hc := (colourMask_eq_some c x t).mp hx
    exact ⟨fun hb=>hcb (hc.1.symm.trans hb),hx⟩

theorem conditioned_colourMask_none_weight {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (b c : C) (hcb : c≠b) :
    (1-μ.probability (fun x=>x.1=b))*
      ((μ.conditionEvent (fun x=>x.1≠b)).map (colourMask c)).mass none=
        (μ.map (colourMask c)).mass none-μ.probability (fun x=>x.1=b) := by
  have hq := finiteLaw_probability_compl μ (fun x=>x.1=b)
  have he : μ.probability (fun x=>x.1≠b)=1-μ.probability (fun x=>x.1=b) := by linarith
  rw [← he,finiteLaw_conditionEvent_map_weight,finiteLaw_map_mass_probability]
  have hsplit := finiteLaw_probability_split μ (fun x=>colourMask c x=none) (fun x=>x.1=b)
  have hfirst : μ.probability (fun x=>colourMask c x=none ∧ x.1=b)=
      μ.probability (fun x=>x.1=b) := by
    apply finiteLaw_probability_congr
    intro x
    constructor
    · exact And.right
    · intro hb
      exact ⟨(colourMask_eq_none c x).mpr (fun hc=>hcb (hc.symm.trans hb)),hb⟩
  have hsecond : μ.probability (fun x=>colourMask c x=none ∧ ¬x.1=b)=
      μ.probability (fun x=>x.1≠b ∧ colourMask c x=none) := by
    apply finiteLaw_probability_congr
    intro x
    exact and_comm
  rw [hfirst,hsecond] at hsplit
  linarith

theorem conditioned_colourMask_l1 {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (b c : C) (hcb : c≠b)
    (hq : 0<1-μ.probability (fun x=>x.1=b)) :
    (((μ.conditionEvent (fun x=>x.1≠b)).map (colourMask c))).l1Distance (μ.map (colourMask c))=
      2*μ.probability (fun x=>x.1=b)*μ.probability (fun x=>x.1=c)/
        (1-μ.probability (fun x=>x.1=b)) := by
  let a := μ.probability (fun x=>x.1=b)
  let p := μ.probability (fun x=>x.1=c)
  let q := 1-a
  let ν := (μ.conditionEvent (fun x=>x.1≠b)).map (colourMask c)
  let ν₀ := μ.map (colourMask c)
  have ha : 0≤a := finiteLaw_probability_nonneg _ _
  have hp : 0≤p := finiteLaw_probability_nonneg _ _
  have hs (t : Bool) : ν.mass (some t)-ν₀.mass (some t)=a*ν₀.mass (some t)/q := by
    have hh := conditioned_colourMask_some_weight μ b c hcb t
    change q*ν.mass (some t)=ν₀.mass (some t) at hh
    apply (eq_div_iff hq.ne').mpr
    dsimp only [q] at *
    nlinarith
  have hn : ν₀.mass none-ν.mass none=a*p/q := by
    have hh := conditioned_colourMask_none_weight μ b c hcb
    have hnone := colourMask_mass_none μ c
    change q*ν.mass none=ν₀.mass none-a at hh
    change ν₀.mass none=1-p at hnone
    apply (eq_div_iff hq.ne').mpr
    dsimp only [q] at *
    nlinarith
  have hs0 (t : Bool) : 0≤a*ν₀.mass (some t)/q := div_nonneg (mul_nonneg ha (ν₀.nonneg _)) hq.le
  have hn0 : 0≤a*p/q := div_nonneg (mul_nonneg ha hp) hq.le
  change ν.l1Distance ν₀=2*a*p/q
  unfold FiniteLaw.l1Distance
  rw [Fintype.sum_option,Fintype.sum_bool]
  rw [abs_sub_comm (ν.mass none) (ν₀.mass none),hn,hs true,hs false,
    abs_of_nonneg hn0,abs_of_nonneg (hs0 true),abs_of_nonneg (hs0 false)]
  have he := colourMask_some_sum μ c
  change ν₀.mass (some true)+ν₀.mass (some false)=p at he
  calc
    _ = a*p/q+a*(ν₀.mass (some true)+ν₀.mass (some false))/q := by ring
    _ = _ := by rw [he];ring

end Oberwolfach
