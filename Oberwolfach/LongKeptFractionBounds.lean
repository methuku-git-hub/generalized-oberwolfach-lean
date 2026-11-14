module

public import Oberwolfach.LongAssignedSeedTargets

@[expose] public section
/-! The retained fraction remains a genuine vertex proportion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U]

theorem long_kept_fraction_bounds (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ) (i:Fin K) (u:U):
    0≤longAssignedKeptFraction F hF K θ i u ∧ longAssignedKeptFraction F hF K θ i u≤1 :=by
  have hn':0<(n:ℝ):=by exact_mod_cast hn
  have hfrac0:0≤ordinaryAssignedFraction F hF K u (some i):=by
    unfold ordinaryAssignedFraction
    positivity
  have hfrac1:ordinaryAssignedFraction F hF K u (some i)≤1:=by
    unfold ordinaryAssignedFraction
    apply (div_le_one hn').2
    have hcard:(Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card≤n:=by
      calc
        _ ≤ (Finset.univ:Finset (Fin n)).card:=Finset.card_le_card (Finset.filter_subset _ _)
        _ = n:=by simp
    exact_mod_cast hcard
  unfold longAssignedKeptFraction
  split_ifs <;> constructor <;> first | assumption | norm_num

theorem long_kept_frequency_target_abs_le_order (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ)
    (hθ0:0≤θ) (hθ1:θ≤1) (i:Fin K) (u:U):
    |(1-θ)*longAssignedKeptFraction F hF K θ i u*(n:ℝ)|≤n :=by
  obtain ⟨hf0,hf1⟩:=long_kept_fraction_bounds hn F hF θ i u
  have hn0:0≤(n:ℝ):=by positivity
  have hmul:0≤(1-θ)*longAssignedKeptFraction F hF K θ i u:=mul_nonneg (by linarith) hf0
  have hmul1:(1-θ)*longAssignedKeptFraction F hF K θ i u≤1:=by nlinarith
  rw [abs_of_nonneg (mul_nonneg hmul hn0)]
  nlinarith
end Oberwolfach
