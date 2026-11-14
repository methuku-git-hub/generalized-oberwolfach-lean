module

public import Oberwolfach.ColorClassSelection

@[expose] public section

/-! The independent colour-class selection step in the weighted matching
argument, with its exact probability law and one event for every fixed test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {E I C V J : Type*} [Fintype E] [Fintype I] [Fintype C] [Nonempty C]
    [DecidableEq E] [DecidableEq I] [DecidableEq C] [DecidableEq V]

theorem colorClassLottery_expectation (part : E → I) (color : E → C) (w : E → ℝ) :
    (FiniteLaw.pi (fun _ : I=>FiniteLaw.uniform C)).expectation
      (fun σ=>∑ i,colorClassWeight part color w i (σ i))=(∑ e,w e)/Fintype.card C := by
  let : MeasurableSpace C := ⊤
  let : MeasurableSingletonClass C := ⟨fun _=>trivial⟩
  calc
    _ = ∑ i,(FiniteLaw.pi (fun _ : I=>FiniteLaw.uniform C)).expectation
        (fun σ=>colorClassWeight part color w i (σ i)) := by
      unfold FiniteLaw.expectation
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i,(FiniteLaw.uniform C).expectation (colorClassWeight part color w i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact finiteLaw_coordinate_expectation _ i _
    _ = ∑ i,(∑ c,colorClassWeight part color w i c)/Fintype.card C := by
      simp_rw [finiteLaw_uniform_expectation]
    _ = _ := by rw [← Finset.sum_div,colorClassWeight_total]

theorem colorClassLottery_matching
    (R : E → Finset V) (part : E → I) (color : E → C)
    (hparts : ∀ e f,part e≠part f → Disjoint (R e) (R f))
    (hcolor : ∀ e f,e≠f → part e=part f → color e=color f → Disjoint (R e) (R f))
    (T : Finset J) (w : J → E → ℝ) (B : J → I → ℝ) (t : J → ℝ)
    (hw : ∀ j∈T,∀ e,0≤w j e)
    (hB : ∀ j∈T,∀ i c,colorClassWeight part color (w j) i c≤B j i)
    (ht : ∀ j∈T,0≤t j)
    (hsmall : (∑ j∈T,2*Real.exp (-2*(t j)^2/(∑ i,(B j i)^2)))<1) :
    ∃ M : Finset E,
      (∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) ∧
      (∀ j∈T,|(∑ e∈M,w j e)-(∑ e,w j e)/Fintype.card C|<t j) := by
  let μ := FiniteLaw.pi (fun _ : I=>FiniteLaw.uniform C)
  let X (j : J) (σ : I → C) := ∑ i,colorClassWeight part color (w j) i (σ i)
  have hnonneg (j : J) (hj : j∈T) (i : I) : 0≤B j i :=
    (colorClassWeight_nonneg part color (w j) (hw j hj) i (Classical.choice (inferInstance : Nonempty C))).trans
      (hB j hj i _)
  have htail (j : J) (hj : j∈T) : μ.probability (fun σ=>t j≤|X j σ-μ.expectation (X j)|)≤
      2*Real.exp (-2*(t j)^2/(∑ i,(B j i)^2)) := by
    exact finiteLaw_boundedDifferences (fun _ : I=>FiniteLaw.uniform C) (X j) (B j)
      (hnonneg j hj)
      (colorClassWeight_coordinate_change part color (w j) (hw j hj) (B j) (hB j hj)) (ht j hj)
  obtain ⟨σ,_hσ,hgood⟩ := finiteLaw_common_event_exists μ T
    (fun j σ=>t j≤|X j σ-μ.expectation (X j)|)
    (fun j=>2*Real.exp (-2*(t j)^2/(∑ i,(B j i)^2))) htail hsmall
  refine ⟨colorClassSelection part color σ,colorClassSelection_matching R part color hparts hcolor σ,?_⟩
  intro j hj
  have hh := lt_of_not_ge (hgood j hj)
  change |(∑ i,colorClassWeight part color (w j) i (σ i))-
    (FiniteLaw.pi (fun _ : I=>FiniteLaw.uniform C)).expectation
      (fun σ=>∑ i,colorClassWeight part color (w j) i (σ i))|<t j at hh
  rw [colorClassLottery_expectation] at hh
  rwa [colorClassSelection_weight]

end Oberwolfach
