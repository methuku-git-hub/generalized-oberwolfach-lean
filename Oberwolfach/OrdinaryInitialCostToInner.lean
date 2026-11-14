module

public import Oberwolfach.MarkedVortexInnerBalanceScale

@[expose] public section
/-! A small ambient linear edit bound fits the first inner-vortex budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_cost_to_inner
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (hε:0<ε) (hm:0<mv) (η ζ cost:ℝ) (hζ:0≤ζ)
    (hsmall:15*η≤ζ*ε/2) (hcost:cost≤15*η*Fintype.card V):
    cost≤ζ*(markedVortexInnerVertices Q 0).card :=by
  have hsize:(ε/2)*(Fintype.card V:ℝ)≤(markedVortexInnerVertices Q 0).card:=by
    have hinner: (markedVortexInnerVertices Q 0).card=(Q.vertices 1).card:=by
      rw [(marked_vortex_inner_cardinalities Q 0).1,Q.extendedVertices_eq (by have hh:=Q.length_pos;omega)]
    rw [hinner]
    have hh:=(Q.consecutive_size_bounds hε hm Q.length_pos).1
    rw [Q.initial] at hh
    simp only [Finset.card_univ] at hh
    nlinarith
  have hn:(0:ℝ)≤Fintype.card V:=by positivity
  have hb:=mul_le_mul_of_nonneg_right hsmall hn
  have hs:=mul_le_mul_of_nonneg_left hsize hζ
  nlinarith
end Oberwolfach
