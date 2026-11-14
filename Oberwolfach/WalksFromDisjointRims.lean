module

public import Oberwolfach.MarkedPackedWheelDirectedEdges

@[expose] public section
/-! Runs built from disjoint wheel rim labels and separated terminal labels
have disjoint vertex supports. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem walks_disjoint_from_separated_rim_labels
    {V I J A B:Type} [DecidableEq V]
    (G:SimpleGraph V) {a₁ b₁ a₂ b₂:V} (q₁:G.Walk a₁ b₁) (q₂:G.Walk a₂ b₂)
    (C:I→A→V) (D:J→B→V)
    (h₁:∀x,x∈q₁.support ↔ x=b₁ ∨ ∃i:I,∃a:A,C i a=x)
    (h₂:∀x,x∈q₂.support ↔ x=b₂ ∨ ∃j:J,∃b:B,D j b=x)
    (hend:b₁≠b₂) (h₁₂:∀j b,b₁≠D j b) (h₂₁:∀i a,b₂≠C i a)
    (hdis:∀i j a b,C i a≠D j b):
    Disjoint q₁.support.toFinset q₂.support.toFinset:=by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases (h₁ x).mp (List.mem_toFinset.mp hx) with he₁|⟨i,a,hi⟩
  · rcases (h₂ x).mp (List.mem_toFinset.mp hy) with he₂|⟨j,b,hj⟩
    · exact hend (he₁.symm.trans he₂)
    · exact h₁₂ j b (he₁.symm.trans hj.symm)
  · rcases (h₂ x).mp (List.mem_toFinset.mp hy) with he₂|⟨j,b,hj⟩
    · exact h₂₁ i a (he₂.symm.trans hi.symm)
    · exact hdis i j a b (hi.trans hj.symm)
end Oberwolfach
