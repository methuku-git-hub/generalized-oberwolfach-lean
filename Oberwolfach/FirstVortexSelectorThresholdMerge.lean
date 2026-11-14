module

public import Mathlib.Tactic

@[expose] public section
/-! Increase the selector's graph-order threshold to include the actual host
threshold without changing its selected event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selector_threshold_merge
    (N NHostGeom:ℕ) (P:ℕ→Prop)
    (h:∃NHost:ℕ,∀n:ℕ,max (max N NHost) 1≤n→P n):
    ∃NHost:ℕ,NHostGeom≤NHost ∧ ∀n:ℕ,max (max N NHost) 1≤n→P n :=by
  obtain ⟨NHost,hHost⟩:=h
  refine ⟨max NHostGeom NHost,le_max_left _ _,?_⟩
  intro n hn
  apply hHost n
  omega
end Oberwolfach
