module

public import Oberwolfach.PrescribedSourceComponentSize
public import Oberwolfach.PrescribedUnifiedComponentBudget

@[expose] public section
/-! The original source-size, saturation and degree bounds supply all five
component-embedding budgets without adding a new size hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_all_component_budgets
    (Q A:Finset X) (as:List X) (ha:as.Nodup)
    (hsub:A∪as.toFinset⊆Q) (hdis:Disjoint A as.toFinset)
    (f:X→V) (S:Finset V) (M β δ n:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤n) (hQ:(Q.card:ℝ)≤δ*n)
    (hS:(S.card:ℝ)≤Real.sqrt δ*n) (hM0:0≤M) (hM:M≤8*Real.sqrt δ*n):
    let b:ℝ:=(A.image f∪S).card;
    b+as.length+2+M<β*n ∧ b+as.length+1+M<β*n ∧
    b+as.length+2+2*M<β*n ∧ b+(as.length+1:ℕ)+2+2*M<β*n := by
  intro b
  have hs:=prescribed_source_component_size Q A as ha hsub hdis δ n hQ
  have hb:=prescribed_unified_component_budget A f S as.length M β δ n hβ hβ1 hδ hδbound hnβ hs hS hM
  dsimp [b] at *
  push_cast at *
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith
end Oberwolfach
