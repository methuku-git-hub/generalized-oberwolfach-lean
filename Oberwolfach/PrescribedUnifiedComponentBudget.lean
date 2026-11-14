module

public import Oberwolfach.PrescribedEmbeddingCycleSlack

@[expose] public section
/-! A single numerical margin supplies every path and cycle component budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_unified_component_budget
    (A:Finset X) (f:X→V) (S:Finset V) (q:ℕ) (M β δ n:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤n) (hsource:(A.card:ℝ)+q≤δ*n)
    (hS:(S.card:ℝ)≤Real.sqrt δ*n) (hM:M≤8*Real.sqrt δ*n):
    ((A.image f∪S).card:ℝ)+q+3+2*M<β*n := by
  have hcard:(A.image f).card≤A.card:=Finset.card_image_le
  have hcardR:((A.image f).card:ℝ)≤A.card:=by exact_mod_cast hcard
  have hunion:((A.image f∪S).card:ℝ)≤(A.image f).card+S.card:=by exact_mod_cast Finset.card_union_le (A.image f) S
  have hslack:=prescribed_embedding_cycle_slack β δ n hβ hβ1 hδ hδbound hnβ
  nlinarith
end Oberwolfach
