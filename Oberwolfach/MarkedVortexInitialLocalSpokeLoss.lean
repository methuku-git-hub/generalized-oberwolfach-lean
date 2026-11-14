module

public import Oberwolfach.MarkedVortexInitialLocalAgreement

@[expose] public section
/-! Restrict the correction's physical inner-column loss to the level-zero type. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_local_spoke_loss
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (H H':Bool→V→U→Prop) (c:ℝ)
    (hNoNew:∀u v,v∈Q.extendedVertices 1→H' false v u→H false v u)
    (hLoss:∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
      c*((markedVortexInnerVertices Q 0).card:ℝ)):
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let I:=markedVortexInnerVertices Q 0;
    (∀u v,v∈I→H' false (f v) (g u)→H false (f v) (g u)) ∧
    (∀u,((I.filter (fun v=>H false (f v) (g u) ∧ ¬H' false (f v) (g u))).card:ℝ)≤c*(I.card:ℝ)):=by
  intro f g I
  have hf:∀v,v∈I→f v∈Q.extendedVertices 1:=by
    intro v hv
    change v.val∈Q.extendedVertices 1
    simpa only [I,markedVortexInnerVertices,Finset.mem_filter,Finset.mem_univ,true_and,zero_add] using hv
  refine ⟨?_,?_⟩
  · intro u v hv hh;exact hNoNew (g u) (f v) (hf v hv) hh
  · intro u
    have hcard:(I.filter (fun v=>H false (f v) (g u) ∧ ¬H' false (f v) (g u))).card≤
        ((Q.extendedVertices 1).filter (fun v=>H false v (g u) ∧ ¬H' false v (g u))).card:=by
      apply Finset.card_le_card_of_injOn f
      · intro v hv
        obtain ⟨hvI,hvH,hvH'⟩:=Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hf v hvI,hvH,hvH'⟩
      · intro a ha b hb hab;exact f.injective hab
    have hh:((I.filter (fun v=>H false (f v) (g u) ∧ ¬H' false (f v) (g u))).card:ℝ)≤
        (((Q.extendedVertices 1).filter (fun v=>H false v (g u) ∧ ¬H' false v (g u))).card:ℝ):=by exact_mod_cast hcard
    exact hh.trans (hLoss (g u))
end Oberwolfach
