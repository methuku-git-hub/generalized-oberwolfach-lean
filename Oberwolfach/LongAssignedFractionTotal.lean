module

public import Oberwolfach.LongKeptFractionBounds

@[expose] public section
/-! The original preparation classes partition every factor's vertices; the
small discarded classes lose at most θ/100 of their total mass. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_fraction_partition
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (u:U):
    ordinaryAssignedFraction F hF K u none +
      ∑i:Fin K,ordinaryAssignedFraction F hF K u (some i)=1:=by
  let f:=fun v:Fin n=>longPreparationCycleClass (F u) (hF u) K v
  have hcard:(Finset.univ:Finset (Fin n)).card=
      ∑j:Option (Fin K),((Finset.univ:Finset (Fin n)).filter (fun v=>f v=j)).card:=by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    exact Finset.mem_univ _
  have hnR:(n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  have hc:((n:ℕ):ℝ)=∑j:Option (Fin K),
      (((Finset.univ:Finset (Fin n)).filter (fun v=>f v=j)).card:ℝ):=by
    exact_mod_cast (by simpa only [Finset.card_univ,Fintype.card_fin] using hcard : n=∑j:Option (Fin K),((Finset.univ:Finset (Fin n)).filter (fun v=>f v=j)).card)
  simp only [Fintype.sum_option] at hc
  unfold ordinaryAssignedFraction
  change (((Finset.univ:Finset (Fin n)).filter (fun v=>f v=none)).card:ℝ)/n +
    ∑i:Fin K,(((Finset.univ:Finset (Fin n)).filter (fun v=>f v=some i)).card:ℝ)/n=1
  rw [←Finset.sum_div,←add_div,←hc]
  exact div_self hnR

theorem long_assigned_retained_fraction_mass
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ) (hθ:0≤θ) (u:U):
    1-θ/100≤ordinaryAssignedFraction F hF K u none+∑i:Fin K,longAssignedKeptFraction F hF K θ i u:=by
  have hbound:∀i:Fin K,ordinaryAssignedFraction F hF K u (some i)≤
      longAssignedKeptFraction F hF K θ i u+θ/(100*(K:ℝ)):=by
    intro i
    unfold longAssignedKeptFraction
    split_ifs with h
    · have hh:0≤θ/(100*(K:ℝ)):=by positivity
      linarith
    · linarith
  have hsum:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin K)))=>hbound i)
  simp only [Finset.sum_add_distrib,Finset.sum_const_zero,Finset.sum_const,Fintype.card_fin,nsmul_eq_mul] at hsum
  simp only [Finset.card_univ,Fintype.card_fin] at hsum
  have hK0:(K:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hK)
  have hcancel:(K:ℝ)*(θ/(100*(K:ℝ)))=θ/100:=by field_simp
  rw [hcancel] at hsum
  have hp:=long_assigned_fraction_partition (K:=K) hn F hF u
  linarith
end Oberwolfach
