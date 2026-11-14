module

public import Oberwolfach.OrdinaryCandidateClassReservation

@[expose] public section
/-! The selected component reserve is bounded directly by its actual
cycle-class frequency; no cutoff-dependent upper bound is built into this predicate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryClassReserveBound {n K:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (s:ℝ):Prop :=
    ∀u,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n
end Oberwolfach
