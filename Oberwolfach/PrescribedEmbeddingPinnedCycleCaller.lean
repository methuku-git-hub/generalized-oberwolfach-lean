module

public import Oberwolfach.ExtendingListPinnedCycle
public import Oberwolfach.PrescribedEmbeddingCycleSlack
public import Oberwolfach.PrescribedEmbeddingLabelBudget
public import Oberwolfach.PrescribedEmbeddingSourceBudget

@[expose] public section
/-! The one-prescribed-vertex cycle construction under the original
square-root, source-size, saturation and forbidden-degree budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_embedding_pinned_cycle_of_source_budgets
    {X V:Type} [DecidableEq X] [Fintype V] [DecidableEq V]
    (Q A C:Finset X) (φ:X→V) (hAC:Disjoint A C)
    (hsub:A∪C⊆Q) (hinj:Set.InjOn φ A) (S L:Finset V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ))
    (hQ:(Q.card:ℝ)≤δ*Fintype.card V)
    (hS:(S.card:ℝ)≤Real.sqrt δ*Fintype.card V)
    (D:V→V→Prop) (hext:IsExtendingList D L β) (F:SimpleGraph V)
    (hF:∀ v,(F.degree v:ℝ)≤8*Real.sqrt δ*Fintype.card V)
    (x:V) (ℓ:ℕ) (hℓ:3≤ℓ) (hC:C.card+1=ℓ):
    ∃ xs:List V,xs.length=ℓ-1 ∧ xs.Nodup ∧
      (∀ z∈xs,z∈L ∧ z∉(A.image φ∪S) ∧ z≠x) ∧ DirectedPathThrough D F x x xs := by
  let n:ℝ:=Fintype.card V
  let M:ℝ:=8*Real.sqrt δ*n
  have hsrcNat:=prescribed_embedding_assigned_and_unembedded_budget Q A C φ hAC hsub hinj
  have hsrc:(A.image φ).card+C.card≤δ*n:=by
    have hh:(((A.image φ).card+C.card:ℕ):ℝ)≤(Q.card:ℝ):=by exact_mod_cast hsrcNat
    dsimp [n] at *
    push_cast at hh
    linarith
  have hlabel:=prescribed_embedding_label_budget (A.image φ) S C.card (Real.sqrt δ*n) δ n hsrc (by simpa [n] using hS)
  have hlabel':(((A.image φ∪S).card:ℕ):ℝ)+ℓ≤Real.sqrt δ*n+δ*n+1:=by
    rw [←hC]
    exact hlabel
  have hbud:=prescribed_embedding_cycle_budget β δ n M (((A.image φ∪S).card:ℕ):ℝ) ℓ hβ hβ1 hδ hδbound (by simpa [n] using hnβ) hlabel' (by simp [M])
  have hM:0≤M:=by dsimp [M,n];positivity
  have hF':∀ v,(F.degree v:ℝ)≤M:=by simpa [M,n] using hF
  exact extending_list_embed_pinned_cycle D L β hext F M hM hF' (A.image φ∪S) x ℓ hℓ (by simpa [n] using hbud)
end Oberwolfach
