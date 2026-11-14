module

public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! Every factor assigned to an ordinary class has enough vertices in its
assigned cycle length to reserve the common fraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_class_reservation {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀ w,(F w).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀ w,AllowedCycleLengths (F w) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s:ℝ) (hs:s≤1/(2*(K:ℝ)))
    (hclass:∀ w,factorPreparationClass (F w) K=some i₀):
    ∀ w,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n := by
  intro w
  have hc: i₀∈factorShortCandidates (F w) K:=
    ((factor_preparation_class hn (F w) (hF w) S (hS w) K hK).2 i₀ (hclass w)).2.2.1
  have hfreq:(1/(2*(K:ℝ)):ℝ)≤
    ((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)).card:ℝ)/n:=
    (Finset.mem_filter.mp hc).2
  have heq:(Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀))=
    (Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)):=by
    apply Finset.filter_congr
    intro v _
    exact (long_preparation_cycle_class (F w) (hF w) K v).2 i₀
  rw [heq]
  exact hs.trans hfreq
end Oberwolfach
