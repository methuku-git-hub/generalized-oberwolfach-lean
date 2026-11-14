module

public import Oberwolfach.OrdinaryClassReservation

@[expose] public section
/-! A specified abundant candidate supplies reservation without requiring it
    to be the classifier's least candidate or excluding its long branch. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_candidate_class_reservation {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s:ℝ) (hs:s≤1/(2*(K:ℝ)))
    (hclass:∀w,i₀∈factorShortCandidates (F w) K):
    ∀w,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n:=by
  intro w
  have hfreq:(1/(2*(K:ℝ)):ℝ)≤
    ((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)).card:ℝ)/n:=
      (Finset.mem_filter.mp (hclass w)).2
  have heq:(Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀))=
    (Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)):=by
    apply Finset.filter_congr
    intro v _
    exact (long_preparation_cycle_class (F w) (hF w) K v).2 i₀
  rw [heq]
  exact hs.trans hfreq
end Oberwolfach
