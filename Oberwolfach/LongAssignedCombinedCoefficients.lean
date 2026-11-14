module

public import Oberwolfach.LongAssignedSamplingRecipe
public import Oberwolfach.LongApproximateCombinedLoads

@[expose] public section
/-! The kept cycle frequencies in the actual long-class recipe give the
same coefficient normalization at ordinary spokes and ordinary rims. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

def longAssignedKeptOrdinaryContribution (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K:ℕ) (θ:ℝ) (i:Fin K) (u:U):ℝ:=
  if θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i) then
    (1-θ)*ordinaryAssignedFraction F hF K u (some i) else 0

theorem long_assigned_approximate_coefficient_balance
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ:ℝ) (u:U):
    longAssignedApproxOrdinaryWeight F hF K m θ u=
      (m:ℝ)*longAssignedApproxMarkedWeight F hF K m θ u+
        ∑i,longAssignedKeptOrdinaryContribution F hF K θ i u:=by
  unfold longAssignedApproxOrdinaryWeight longAssignedKeptOrdinaryContribution
  dsimp only
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem long_assigned_approximate_coefficients_sum_one
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ) (hD:0<D) (hp:0<p)
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hpdef:p=(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)
    (hkdef:k=(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D):
    (∀u,(m:ℝ)*longAssignedApproxMarkedWeight F hF K m θ u/
        longAssignedApproxOrdinaryWeight F hF K m θ u+
        ∑i,longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u=1) ∧
    ((m:ℝ)*k/p+∑i,(∑u,longAssignedKeptOrdinaryContribution F hF K θ i u)/(D*p)=1):=by
  have hbala:=long_assigned_approximate_coefficient_balance F hF K m θ
  exact ⟨long_approximate_spoke_coefficients_sum_one m
      (longAssignedApproxMarkedWeight F hF K m θ) (longAssignedApproxOrdinaryWeight F hF K m θ)
      (longAssignedKeptOrdinaryContribution F hF K θ) hb hbala,
    long_approximate_ordinary_rim_coefficients_sum_one m D p k hD hp
      (longAssignedApproxMarkedWeight F hF K m θ) (longAssignedApproxOrdinaryWeight F hF K m θ)
      (longAssignedKeptOrdinaryContribution F hF K θ) hbala hpdef hkdef⟩
end Oberwolfach
