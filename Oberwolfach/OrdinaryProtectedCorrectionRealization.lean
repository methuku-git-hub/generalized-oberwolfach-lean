module

public import Oberwolfach.OrdinaryProtectedCorrectionCuts

@[expose] public section
/-! A sparse correction in the host with the protected rectangle removed
    is a correction of the original host which preserves that rectangle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_correction_realization
    (r:ℕ) (ξ:ℝ) (Q:SimpleGraph V) (H:V→U→Prop) (T:Finset V) (B:Finset U)
    (JQ:SimpleGraph V) (JH:V→U→Prop)
    (hJQ:JQ≤Q\spanningRestriction Q T)
    (hJH:∀v u,JH v u→H v u ∧ ¬(v∈T ∧ u∈B))
    (hbal:∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card)
    (hrow:∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V)
    (hcol:∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):
    JQ≤Q ∧ (∀v∈T,∀w∈T,¬JQ.Adj v w) ∧
    (∀v u,JH v u→H v u ∧ ¬(v∈T ∧ u∈B)) ∧
    (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
    (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
    (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):=by
  refine ⟨hJQ.trans sdiff_le,?_,hJH,hbal,hdiv,hrow,hcol⟩
  intro v hv w hw he
  have hNo:¬(spanningRestriction Q T).Adj v w:=(hJQ he).2
  exact hNo ((spanningRestriction_adj Q T v w).mpr ⟨(hJQ he).1,hv,hw⟩)
end Oberwolfach
