module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedClassRecipeValid
public import Oberwolfach.CandidateOrdinaryAssignedSamplingParametersDirectReserve
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! The actual class sampling probabilities satisfy the interval-law
hypotheses; the construction still uses the original supplied factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_assigned_class_recipe_valid_candidate_direct_reserve {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀ w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤s) (hs1:s≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀ w,AllowedCycleLengths (F w) S)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ s):
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let sco:=ordinaryAssignedSpokeProbability F hF K i₀ s θ c;
    (∀ w j,0≤q w j) ∧ (∀ w,∑ j,q w j≤1/8) ∧
    (∀ w j,0≤sco w j) ∧ (∀ w,∑ j,sco w j ≤ intervalUncoveredProbability d (∑ j,q w j)) ∧
    (∀w,sco w false=s) := by
  have h:=ordinary_class_assigned_sampling_parameters_candidate_direct_reserve hn F hF K hK i₀ s θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize S hS hClassReserve
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro w j
    convert h.2.1 w j using 1 <;>
      simp only [ordinaryAssignedMarkedProbability,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  · intro w
    convert h.2.2.1 w using 1 <;>
      simp only [ordinaryAssignedMarkedProbability,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  · intro w j
    convert h.2.2.2.1 w j using 1 <;>
      simp only [ordinaryAssignedSpokeProbability,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  · intro w
    convert h.2.2.2.2.1 w using 1 <;>
      simp only [ordinaryAssignedSpokeProbability,ordinaryAssignedShortWeight,ordinaryAssignedMarkedProbability,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  · intro w;rfl
  all_goals try (with_reducible rfl)
end Oberwolfach
