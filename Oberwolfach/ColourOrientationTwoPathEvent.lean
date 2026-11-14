module

public import Oberwolfach.ColourOrientationTwoPaths

@[expose] public section

/-! Simultaneous directed two-step counts for every distinct ordered root pair.
No separation condition is imposed on the two roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V] {R : ℕ}

theorem sampledColourOrientation_twoPaths_common_event
    (G E : SimpleGraph V) (hEG : E≤G)
    (ρ : Fin R→ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1) (a : Fin R)
    {t : ℝ} (ht : 0≤t) :
    1-2*(Fintype.card V:ℝ)^2*Real.exp (-t^2/Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
      (fun σ=>∀ x y,x≠y →
        |(eligibleTwoPathCount E (sampledColourOrientation G σ a) x y:ℝ)-
          ((E.neighborFinset x∩E.neighborFinset y).card:ℝ)*(ρ a/2)^2|<t) := by
  let I := {z : V×V // z.1≠z.2}
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)
  have hh := finiteLaw_common_event_lower μ (Finset.univ : Finset I)
    (fun z σ=>t≤|(eligibleTwoPathCount E (sampledColourOrientation G σ a) z.val.1 z.val.2:ℝ)-
      ((E.neighborFinset z.val.1∩E.neighborFinset z.val.2).card:ℝ)*(ρ a/2)^2|)
    (fun _=>2*Real.exp (-t^2/Fintype.card V))
    (fun z _=>sampledColourOrientation_twoPath_tail G E hEG ρ hρ hsum a z.property ht)
  have hi : Fintype.card I≤Fintype.card V^2 := by
    exact (Fintype.card_subtype_le _).trans_eq (by simp [pow_two])
  have hiR : (Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^2 := by exact_mod_cast hi
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] at hh
  have hbudget : (Fintype.card I:ℝ)*(2*Real.exp (-t^2/Fintype.card V))≤
      2*(Fintype.card V:ℝ)^2*Real.exp (-t^2/Fintype.card V) := by
    nlinarith only [mul_le_mul_of_nonneg_right hiR
      (show 0≤2*Real.exp (-t^2/Fintype.card V) by positivity)]
  apply ((sub_le_sub_left hbudget 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy
  exact hσ ⟨(x,y),hxy⟩

theorem commonNeighbours_lower_of_minDegree
    (P : SimpleGraph V) (γ : ℝ)
    (hP : ∀ v,(1/2+γ)*Fintype.card V≤(P.degree v:ℝ)) (x y : V) :
    2*γ*Fintype.card V≤((P.neighborFinset x∩P.neighborFinset y).card:ℝ) := by
  have he := Finset.card_inter_add_card_union (P.neighborFinset x) (P.neighborFinset y)
  have hu := Finset.card_le_univ (P.neighborFinset x∪P.neighborFinset y)
  have he' : ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)+
      ((P.neighborFinset x∪P.neighborFinset y).card:ℝ)=(P.degree x:ℝ)+P.degree y := by
    exact_mod_cast (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using he)
  have hu' : ((P.neighborFinset x∪P.neighborFinset y).card:ℝ)≤Fintype.card V := by exact_mod_cast hu
  linarith [hP x,hP y]

end Oberwolfach
