module

public import Oberwolfach.OrdinaryInnerTargetCapacity

@[expose] public section

/-! A capacity estimate uniform over bounded sets can be applied separately
to each hub's uncovered targets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_indexed_target_capacity
    {U V:Type} [Fintype U] [DecidableEq U] [DecidableEq V]
    (T Old:U→Finset V) (pres remaining:U→ℕ) (cost:ℕ) (bound:ℝ)
    (hcap:∀Z:Finset V,(Z.card:ℝ)≤bound→
      ∀u,8*pres u+cost+4*Z.card+10≤remaining u)
    (hsize:∀u,((T u\Old u).card:ℝ)≤bound):
    ∀u,8*pres u+cost+4*(T u\Old u).card+10≤remaining u :=by
  intro u
  exact hcap (T u\Old u) (hsize u) u
end Oberwolfach
