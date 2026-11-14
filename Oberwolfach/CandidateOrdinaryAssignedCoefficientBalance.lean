module

public import Oberwolfach.OrdinaryAssignedCoefficientBalance
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedFrequencyCoefficient
public import Oberwolfach.OrdinaryAssignedFrequencyCoefficient
public import Oberwolfach.LongAssignedShortClassZero
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! The actual ordinary coefficients satisfy the matching balance and
vanish on the two padded indices which cannot represent simple cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_coefficient_balance_candidate
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K):
    ∀u,(∑i,ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i)*
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c u+
      (c-1)*ordinaryAssignedLongWeight F hF K θ c u=
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c u :=by
  have hreserve:=ordinary_candidate_class_reservation hn F hF S hS K hK i₀ rsv hsclass hclass
  intro u
  have hh:=ordinary_factor_frequency_weight_allocation hn (F u) (hF u) K hK i₀ rsv θ c
    hs0 hs1 hθ.le hθ1 hc (hreserve u)
  simpa only [ordinaryAssignedFrequencyCoefficient,ordinaryAssignedKeptFraction,
      ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2

theorem ordinary_assigned_short_padded_coefficient_zero_candidate
    {n:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀ i:Fin K) (hi:i.val+1<3)
    (rsv θ c:ℝ) (hs:0≤rsv) (hθ:0<θ) (u:U):
    ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i=0 ∧
    ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i=0 :=by
  have hf:=long_assigned_fraction_below_three_zero F hF K i hi u
  have hcut:0<θ/(100*(K:ℝ)):=by
    have hk:(0:ℝ)<K:=by exact_mod_cast hK
    positivity
  have hz:ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i=0:=by
    unfold ordinaryAssignedKeptFraction
    rw [hf]
    by_cases h:i=i₀ <;> simp [h,show -rsv<θ/(100*(K:ℝ)) by linarith,hcut]
  exact ⟨hz,by simp [ordinaryAssignedFrequencyCoefficient,hz]⟩
end Oberwolfach
