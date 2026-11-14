module

public import Oberwolfach.OrdinaryAssignedFrequencyCoefficient
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.OrdinaryFactorWeightAllocation
public import Oberwolfach.OrdinaryClassReservation
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! The actual assigned-factor cycle frequencies determine the
per-hub coefficients used by the ordinary approximate wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_frequency_coefficient_candidate
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s θ c:ℝ)
    (hs0:0≤s) (hs1:s≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:s≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K):
    ∀w,0<ordinaryAssignedShortWeight F hF K i₀ s θ c w ∧
      (∀i,0≤ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i ∧
        ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i≤1/ordinaryAssignedShortWeight F hF K i₀ s θ c w) ∧
      (∀i,ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i*
        ordinaryAssignedShortWeight F hF K i₀ s θ c w=(1-θ)*ordinaryAssignedKeptFraction F hF K i₀ s θ w i) :=by
  have hreserve:=ordinary_candidate_class_reservation hn F hF S hS K hK i₀ s hsclass hclass
  intro w
  have hh:=ordinary_factor_frequency_weight_allocation hn (F w) (hF w) K hK i₀ s θ c hs0 hs1 hθ.le hθ1 hc (hreserve w)
  have hb:0<ordinaryAssignedShortWeight F hF K i₀ s θ c w:=by
    convert hh.1 using 1 <;>
      simp only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  have hη:∀i,0≤ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i ∧
      ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i≤1/ordinaryAssignedShortWeight F hF K i₀ s θ c w:=by
    intro i
    convert hh.2.1 i using 1 <;>
      simp only [ordinaryAssignedFrequencyCoefficient,ordinaryAssignedKeptFraction,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  refine ⟨hb,hη,?_⟩
  intro i
  unfold ordinaryAssignedFrequencyCoefficient
  exact div_mul_cancel₀ _ (ne_of_gt hb)
end Oberwolfach
