module

public import Oberwolfach.LongAssignedSeedTargets

@[expose] public section
/-! Bounds for every ordinary seed coefficient, including indices with no
retained vertices at any hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

theorem long_assigned_all_ordinary_seed_coefficients
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ:ℝ) (hθ0:0≤θ) (hθ1:θ≤1)
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u):
    ∀i:Fin K,∀u,
      0≤longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u ∧
      longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u≤
        1/longAssignedApproxOrdinaryWeight F hF K m θ u :=by
  intro i u
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hfrac0:0≤ordinaryAssignedFraction F hF K u (some i):=by
    unfold ordinaryAssignedFraction
    positivity
  have hfrac1:ordinaryAssignedFraction F hF K u (some i)≤1:=by
    unfold ordinaryAssignedFraction
    apply (div_le_one hnR).2
    have hh:(Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card≤n:=by
      calc
        _ ≤ (Finset.univ:Finset (Fin n)).card:=Finset.card_le_card (Finset.filter_subset _ _)
        _ = n:=by simp
    exact_mod_cast hh
  have hc0:0≤longAssignedKeptOrdinaryContribution F hF K θ i u:=by
    unfold longAssignedKeptOrdinaryContribution
    split_ifs <;> positivity
  have hc1:longAssignedKeptOrdinaryContribution F hF K θ i u≤1:=by
    unfold longAssignedKeptOrdinaryContribution
    split_ifs with h
    · have hh:=mul_le_mul hfrac1 (show 1-θ≤1 by linarith) (by linarith : 0≤1-θ) (by norm_num: (0:ℝ)≤1)
      nlinarith
    · norm_num
  exact ⟨div_nonneg hc0 (hb u).le,div_le_div_of_nonneg_right hc1 (hb u).le⟩
theorem long_assigned_all_ordinary_seed_balance
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ:ℝ) (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u):
    ∀i:Fin K,∀u,
      (longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u)*
        longAssignedApproxOrdinaryWeight F hF K m θ u=
      (1-θ)*longAssignedKeptFraction F hF K θ i u :=by
  intro i u
  rw [div_mul_cancel₀ _ (ne_of_gt (hb u))]
  exact long_assigned_kept_fraction_contribution F hF K θ i u
end Oberwolfach
