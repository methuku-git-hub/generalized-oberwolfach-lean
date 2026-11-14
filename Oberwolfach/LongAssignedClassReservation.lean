module

public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! A factor assigned to the long class satisfies exactly the long-frequency
hypothesis used to construct its marked-class sampling probabilities. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_class_assigned_frequency {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (S:Set ℕ) (hS:∀u,AllowedCycleLengths (F u) S)
    (K:ℕ) (hK:0<K) (hclass:∀u,factorPreparationClass (F u) K=none):
    ∀u,(1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n:=by
  intro u
  exact ((factor_preparation_class hn (F u) (hF u) S (hS u) K hK).1).mp (hclass u)
end Oberwolfach
