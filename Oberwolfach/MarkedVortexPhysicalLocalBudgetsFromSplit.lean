module

public import Oberwolfach.MarkedVortexPhysicalSpokeLossBudget

@[expose] public section
/-! Assemble the local rim, row, and inner-column estimates needed by the
localized terminal chain from bounds for one corrected physical outcome. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_physical_local_budgets_from_split
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0<ε) (hm:0<m) (FR:SimpleGraph V) (H H':Bool→V→U→Prop)
    (cap R S ζ P L:ℝ) (hcap:0≤cap)
    (hR:∀v,v∉Q.extendedVertices 1→(FR.degree v:ℝ)≤R)
    (hRbudget:R≤cap*((markedVortexInnerVertices Q 0).card:ℝ))
    (hS:∀B:Finset U,∀v,v∉Q.extendedVertices 1→
      (∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤S)
    (hSbudget:S≤cap*((markedVortexInnerVertices Q 0).card:ℝ))
    (hNoNew:∀u v,v∈Q.extendedVertices 1→H' false v u→H false v u)
    (hζ:ζ≤cap/128) (hP:P≤cap*(ε*Fintype.card V)/128)
    (hL:2*L≤cap*(ε*Fintype.card V)/128)
    (hloss:∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
      ζ*(Q.extendedVertices 1).card+P+2*L):
    (∀v,v∉Q.extendedVertices 1→(FR.degree v:ℝ)≤cap*((markedVortexInnerVertices Q 0).card:ℝ)) ∧
    (∀B:Finset U,∀v,v∉Q.extendedVertices 1→
      (∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤cap*((markedVortexInnerVertices Q 0).card:ℝ)) ∧
    (∀u v,v∈Q.extendedVertices 1→H' false v u→H false v u) ∧
    (∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
      cap*((markedVortexInnerVertices Q 0).card:ℝ)) :=by
  refine ⟨?_,?_,hNoNew,?_⟩
  · intro v hv;exact (hR v hv).trans hRbudget
  · intro B v hv;exact (hS B v hv).trans hSbudget
  · exact marked_vortex_physical_spoke_loss_budget G D m β ε Q hε hm H H' cap ζ P L hcap hζ hP hL hloss
end Oberwolfach
