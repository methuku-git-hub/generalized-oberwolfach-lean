module

public import Oberwolfach.OrdinaryClassReservation

@[expose] public section
/-! A specified abundant cycle length supports reservation independently of
    the auxiliary least-candidate factor classifier. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reservation_from_specified_abundance {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (i₀:Fin K) (β rsv:ℝ) (hrsv:rsv≤β)
    (hfreq:∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)).card:ℝ)):
    ∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n:=by
  intro w
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have heq:(Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀))=
      (Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)):=by
    apply Finset.filter_congr
    intro v _
    exact (long_preparation_cycle_class (F w) (hF w) K v).2 i₀
  rw [heq]
  apply (le_div_iff₀ hnR).2
  exact (mul_le_mul_of_nonneg_right hrsv hnR.le).trans (hfreq w)
end Oberwolfach
