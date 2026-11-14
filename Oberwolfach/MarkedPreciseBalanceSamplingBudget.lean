module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the two balance-event errors before sampling with the relative
and ambient slack needed by the corrected first parent. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_precise_balance_sampling_budget
    (r:ℕ) (etaBal x:ℝ) (hη:0<etaBal) (hx:0<x):
    ∃eps ζ:ℝ,0<eps ∧ 0<ζ ∧
      eps+((r+4)+2:ℕ)*ζ≤etaBal/2 ∧
      eps+((r+4)+2:ℕ)*ζ≤x/4 :=by
  let a:=min etaBal x
  let e:=a/(100*((r:ℝ)+7))
  have ha:0<a:=by dsimp [a];positivity
  have he:0<e:=by dsimp [e];positivity
  have haη:a≤etaBal:=min_le_left _ _
  have hax:a≤x:=min_le_right _ _
  have heq:e*(100*((r:ℝ)+7))=a:=by dsimp [e];field_simp
  have hr:0≤(r:ℝ):=Nat.cast_nonneg _
  have hbound:(4*((r:ℝ)+7))*e≤a:=by nlinarith only [heq,he,hr]
  refine ⟨e,e,he,he,?_,?_⟩ <;> push_cast <;> nlinarith only [hbound,haη,hax,hη,hx]
end Oberwolfach
