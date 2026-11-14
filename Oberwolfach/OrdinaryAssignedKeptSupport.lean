module

public import Oberwolfach.OrdinaryAssignedFrequencyCoefficient

@[expose] public section
/-! Truncation makes every nonzero kept frequency meet the retained-test
threshold, so summing over retained tests loses no kept mass. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_assigned_kept_fraction_support
    {n K:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ) (u:U) (i:Fin K):
    ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i=0 ∨
      θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i:=by
  by_cases h : ordinaryAssignedFraction F hF K u (some i) - (if i = i₀ then rsv else 0) < θ / (100 * (K : ℝ))
  · left
    simp only [ordinaryAssignedKeptFraction, h, if_pos]
  · right
    simp only [ordinaryAssignedKeptFraction, h, if_false]
    exact le_of_not_gt h

theorem ordinary_assigned_kept_fraction_sum_retained
    {n K:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ) (u:U):
    (∑i∈Finset.univ.filter (fun i:Fin K=>θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i),
      ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)=
      ∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i:=by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hn:¬θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i:=by
    intro hr
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩
  exact (ordinary_assigned_kept_fraction_support F hF i₀ rsv θ u i).resolve_right hn
end Oberwolfach
