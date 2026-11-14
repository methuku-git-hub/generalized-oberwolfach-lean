module

public import Oberwolfach.MarkedSpokeRowSizeFromBalance

@[expose] public section
/-! Reserved ordinary spokes can disappear only through a reference-label
change or the completion image, when the old image and marked endpoints
avoid the reserved labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_spoke_loss_from_completion
    (Hold Hnew:V→U→Prop) (L Old New B Y:U→Finset V)
    (hOld:∀u,Disjoint (Old u) (L u))
    (hEnd:∀u,Disjoint (B u) (L u))
    (hMark:∀u,Disjoint (Y u) (L u))
    (hNew:∀v u,Hnew v u↔v∉Old u∧v∉New u∧v∉B u∧v∉Y u):
    ∀v u,Hold v u→¬Hnew v u→¬(Hold v u↔v∈L u)∨v∈New u:=by
  intro v u hh hn
  by_cases hl:v∈L u
  · right
    by_contra hnew
    apply hn
    apply (hNew v u).mpr
    exact ⟨fun h=>(Finset.disjoint_left.mp (hOld u)) h hl,hnew,
      fun h=>(Finset.disjoint_left.mp (hEnd u)) h hl,
      fun h=>(Finset.disjoint_left.mp (hMark u)) h hl⟩
  · exact Or.inl (fun he=>hl (he.mp hh))

theorem marked_spoke_loss_counts_from_completion
    (Hold Hnew:V→U→Prop) (L Old New B Y:U→Finset V)
    (hOld:∀u,Disjoint (Old u) (L u)) (hEnd:∀u,Disjoint (B u) (L u))
    (hMark:∀u,Disjoint (Y u) (L u))
    (hNew:∀v u,Hnew v u↔v∉Old u∧v∉New u∧v∉B u∧v∉Y u):
    (∀v,((Finset.univ.filter (fun u=>Hold v u∧¬Hnew v u)).card:ℝ)≤
      ((Finset.univ.filter (fun u=>¬(Hold v u↔v∈L u))).card:ℝ)+
      ((Finset.univ.filter (fun u=>v∈New u)).card:ℝ)) ∧
    (∀u,((Finset.univ.filter (fun v=>Hold v u∧¬Hnew v u)).card:ℝ)≤
      ((Finset.univ.filter (fun v=>¬(Hold v u↔v∈L u))).card:ℝ)+(New u).card):=by
  have hh:=marked_spoke_loss_from_completion Hold Hnew L Old New B Y hOld hEnd hMark hNew
  constructor
  · intro v
    have sub:Finset.univ.filter (fun u=>Hold v u∧¬Hnew v u)⊆
        (Finset.univ.filter (fun u=>¬(Hold v u↔v∈L u)))∪(Finset.univ.filter (fun u=>v∈New u)):=by
      intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hu ⊢
      exact hh v u hu.1 hu.2
    have hn:((Finset.univ.filter (fun u=>Hold v u∧¬Hnew v u)).card:ℝ)≤
        (((Finset.univ.filter (fun u=>¬(Hold v u↔v∈L u))).card+
         (Finset.univ.filter (fun u=>v∈New u)).card):ℕ):=by
      exact_mod_cast (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    push_cast at hn
    exact hn
  · intro u
    have sub:Finset.univ.filter (fun v=>Hold v u∧¬Hnew v u)⊆
        (Finset.univ.filter (fun v=>¬(Hold v u↔v∈L u)))∪New u:=by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hv ⊢
      exact hh v u hv.1 hv.2
    have hn:((Finset.univ.filter (fun v=>Hold v u∧¬Hnew v u)).card:ℝ)≤
        (((Finset.univ.filter (fun v=>¬(Hold v u↔v∈L u))).card+(New u).card):ℕ):=by
      exact_mod_cast (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    push_cast at hn
    exact hn
end Oberwolfach
