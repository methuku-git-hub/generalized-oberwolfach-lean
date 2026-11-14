module

public import Oberwolfach.LongOriginalAllowedHostInputs

@[expose] public section
/-! Any indexed family satisfying the original component thresholds admits
one common allowed-length set for the matching selector. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_indexed_allowed_from_threshold {n:ℕ} {U:Type} [Fintype U]
    (θ:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ):
    ∃Allowed:Set ℕ,(∀s∈Allowed,cycleThreshold s≤θ) ∧ ∀w,AllowedCycleLengths (F w) Allowed :=by
  let Allowed:Set ℕ:={s | 3≤s ∧ cycleThreshold s≤θ}
  refine ⟨Allowed,?_,?_⟩
  · intro s hs;exact hs.2
  · intro w v
    rw [reachable_order_eq_component_card (F w) ((F w).connectedComponentMk v) v rfl]
    exact ⟨(component_regular_two_cycle_iso (F w) (hF w) ((F w).connectedComponentMk v)).1,hthreshold w v⟩
end Oberwolfach
