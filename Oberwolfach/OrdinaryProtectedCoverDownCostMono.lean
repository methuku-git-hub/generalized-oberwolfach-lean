module

public import Oberwolfach.OrdinaryProtectedHostCoverDownResult

@[expose] public section
/-! A verified cover-down remains valid under larger trace budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_cover_down_cost_mono
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ)
    (a b cost deepCost:ℝ) (ha:a≤cost) (hb:b≤deepCost)
    (h:OrdinaryProtectedHostCoverDownResult Q F H X T Z W r a b):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W r cost deepCost :=by
  obtain ⟨A,S,hAQ,hSH,hdec,hinside,hbal,hdiv,hcost,hdeep,havoid⟩:=h
  refine ⟨A,S,hAQ,hSH,hdec,hinside,hbal,hdiv,?_,?_,havoid⟩
  · intro w;exact (hcost w).trans ha
  · intro w;exact (hdeep w).trans hb
end Oberwolfach
