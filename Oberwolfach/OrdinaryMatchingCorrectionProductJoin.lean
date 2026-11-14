module

public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.FiniteLawPositiveEventWitness
public import Oberwolfach.FiniteProductRegrouping

@[expose] public section
/-! A matching event on a sampled outcome and a correction event using an
additional coin can be intersected on the same outcome without independence. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_correction_product_join
    {Ω Ξ:Type} [Fintype Ω] [Fintype Ξ] (μ:FiniteLaw Ω) (κ:FiniteLaw Ξ)
    (Match:Ω→Prop) (Correction:Ω×Ξ→Prop) (εM εC:ℝ)
    (hM:1-εM≤μ.probability Match)
    (hC:1-εC≤(μ.prod κ).probability Correction):
    1-εM-εC≤(μ.prod κ).probability (fun z=>Match z.1 ∧ Correction z) ∧
    (0<1-εM-εC→∃z,0<(μ.prod κ).mass z ∧ Match z.1 ∧ Correction z) :=by
  have hM':1-εM≤(μ.prod κ).probability (fun z=>Match z.1):=by
    rw [finiteLaw_prod_first_probability]
    exact hM
  have h:=finiteLaw_intersection_lower (μ.prod κ) (fun z=>Match z.1) Correction εM εC hM' hC
  refine ⟨h,?_⟩
  intro hpos
  exact finiteLaw_positive_mass_witness_of_event (μ.prod κ) (fun z=>Match z.1 ∧ Correction z) (lt_of_lt_of_le hpos h)
end Oberwolfach
