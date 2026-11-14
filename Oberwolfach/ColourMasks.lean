module

public import Oberwolfach.ColourRetentionCoins
public import Oberwolfach.FiniteEventConditioning

@[expose] public section

/-! For one fixed colour, only its presence and its retention coin matter.
The map to Option Bool records none for every other colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def colourMask {C : Type*} (c : C) (x : C×Bool) : Option Bool :=
  if x.1=c then some x.2 else none

theorem colourMask_eq_none {C : Type*} (c : C) (x : C×Bool) :
    colourMask c x=none ↔ x.1≠c := by
  unfold colourMask
  by_cases hc : x.1=c <;> simp [hc]

theorem colourMask_eq_some {C : Type*} (c : C) (x : C×Bool) (b : Bool) :
    colourMask c x=some b ↔ x.1=c ∧ x.2=b := by
  unfold colourMask
  by_cases hc : x.1=c <;> simp [hc]

def maskRetains {V : Type*} (G : SimpleGraph V) (σ : V → Option Bool) (v : V) : Prop :=
  σ v=some true ∧ ∀ u,G.Adj v u → σ u=none

theorem coinRetainedColour_iff_mask
    {V C : Type*} (G : SimpleGraph V) (σ : V → C×Bool) (v : V) (c : C) :
    coinRetainedColour G σ v=some c ↔ maskRetains G (fun u=>colourMask c (σ u)) v := by
  rw [coinRetainedColour_eq_some]
  unfold maskRetains
  simp only [colourMask_eq_some,colourMask_eq_none]
  constructor
  · rintro ⟨hc,hcoin,hkeep⟩
    refine ⟨⟨hc,hcoin⟩,?_⟩
    intro u hu
    simpa only [hc] using hkeep u hu
  · rintro ⟨⟨hc,hcoin⟩,hkeep⟩
    refine ⟨hc,hcoin,?_⟩
    intro u hu
    simpa only [hc] using hkeep u hu

theorem finiteLaw_map_mass_probability {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (f : Ω → Γ) (y : Γ) :
    (μ.map f).mass y=μ.probability (fun x=>f x=y) := rfl

theorem finiteLaw_conditionEvent_map_weight
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (A : Ω → Prop) (f : Ω → Γ) (y : Γ) :
    μ.probability A*((μ.conditionEvent A).map f).mass y=
      μ.probability (fun x=>A x ∧ f x=y) := by
  rw [finiteLaw_map_mass_probability]
  exact finiteLaw_conditionEvent_probability μ A (fun x=>f x=y)

theorem colourMask_mass_none {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (c : C) :
    (μ.map (colourMask c)).mass none=1-μ.probability (fun x=>x.1=c) := by
  rw [finiteLaw_map_mass_probability]
  have he (x : C×Bool) := colourMask_eq_none c x
  rw [finiteLaw_probability_congr μ _ _ he]
  have h := finiteLaw_probability_compl μ (fun x=>x.1=c)
  linarith

theorem colourMask_mass_some {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (c : C) (b : Bool) :
    (μ.map (colourMask c)).mass (some b)=μ.mass (c,b) := by
  rw [finiteLaw_map_mass_probability]
  have he (x : C×Bool) : colourMask c x=some b ↔ x=(c,b) := by
    rw [colourMask_eq_some]
    constructor
    · rintro ⟨h₁,h₂⟩
      exact Prod.ext h₁ h₂
    · rintro rfl
      exact ⟨rfl,rfl⟩
  rw [finiteLaw_probability_congr μ _ _ he,finiteLaw_probability_point]

theorem colourMask_some_sum {C : Type*} [Fintype C]
    (μ : FiniteLaw (C×Bool)) (c : C) :
    (μ.map (colourMask c)).mass (some true)+(μ.map (colourMask c)).mass (some false)=
      μ.probability (fun x=>x.1=c) := by
  have htotal := (μ.map (colourMask c)).total
  rw [Fintype.sum_option,Fintype.sum_bool,colourMask_mass_none] at htotal
  linarith

end Oberwolfach
