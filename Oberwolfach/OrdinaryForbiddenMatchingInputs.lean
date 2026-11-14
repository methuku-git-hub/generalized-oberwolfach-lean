module

public import Oberwolfach.OrdinaryForbiddenRequiredEditDegree

@[expose] public section
/-! Inputs for matching the required graph against the same surviving sample.
The budget contains the original edit, protected reservoir, inner set and
forbidden graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem ordinary_forbidden_matching_inputs
    (Target Sample Reference Protect Bad : SimpleGraph V) (Inner : Finset V) (b a f B : ℝ)
    (hRef : Reference ≤ Sample) (hProtectRef : Protect ≤ Reference) (hBadRef : Disjoint Reference Bad)
    (hEdit : ∀ v, ((Finset.univ.filter (fun w => Xor (Target.Adj v w) (Sample.Adj v w))).card : ℝ) ≤ b)
    (hProtect : ∀ v, (Protect.degree v : ℝ) ≤ a) (hBad : ∀ v, (Bad.degree v : ℝ) ≤ f)
    (hGbudget : b + Inner.card + f ≤ B) (hDelbudget : b + a + Inner.card + f ≤ B) :
    let G := ordinaryForbiddenRequired Target Sample Reference Bad Inner
    let Del := ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner;
    Sample \ (Target \ Protect) ≤ Del ∧ G ≤ Target \ Protect ∧
    (∀ v w, G.Adj v w → ¬(Sample \ Del).Adj v w) ∧
    (∀ v, (G.degree v : ℝ) ≤ B) ∧ (∀ v, (Del.degree v : ℝ) ≤ B) ∧
    Target ⊓ Bad ≤ G ∧ ordinaryProtectedRequired Target Sample Reference Inner ≤ G := by
  intro G Del
  have hr := ordinary_forbidden_required_relations Target Sample Reference Protect Bad Inner hRef hProtectRef hBadRef
  have hd := ordinary_forbidden_required_degree_bounds_of_edit Target Sample Reference Protect Bad Inner b a f hEdit hProtect hBad
  have hlost : Sample \ (Target \ Protect) ≤ Del := by
    intro v w h
    by_contra hn
    exact h.2 (hr.2.1 ⟨h.1, hn⟩)
  refine ⟨hlost, hr.1, hr.2.2.1, ?_, ?_, hr.2.2.2.1, hr.2.2.2.2⟩
  · intro v
    exact le_trans (hd.1 v) hGbudget
  · intro v
    exact le_trans (hd.2 v) hDelbudget
end Oberwolfach
