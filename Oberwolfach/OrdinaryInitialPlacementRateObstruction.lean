module

public import Oberwolfach.OrdinaryTrackedComplementCostBudget
public import Oberwolfach.MarkedVortexInnerBalanceScale

@[expose] public section
/-! The present sufficient initial-edit and protected-size bounds cannot be
combined with the small placement deletion rate. This records a limitation
of this parameter route, not a counterexample to the main theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_placement_rate_obstruction
    (ε ρ₀ δinitial η δplacement b:ℝ)
    (hε:0<ε) (hδi:δinitial≤1)
    (hsmall:15*η≤min δinitial (δinitial*(ρ₀/8))*ε/2)
    (hδp:0≤δplacement) (hδp1:δplacement≤1) (hcap:5*Real.sqrt δplacement≤η)
    (hb:b≤δplacement/8) (hprotected:ε/2≤b/8):False :=by
  have hrate:δplacement≤η:=ordinary_sqrt_cap_controls_residual_rate δplacement η hδp hδp1 hcap
  have hmin:min δinitial (δinitial*(ρ₀/8))≤1:=(min_le_left _ _).trans hδi
  have hscaled:=mul_le_mul_of_nonneg_right hmin hε.le
  nlinarith only [hsmall,hscaled,hrate,hb,hprotected,hε]

theorem ordinary_first_inner_size_forces_placement_rate
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε b:ℝ) (Q:Vortex U P D β ε mv)
    (hε:0<ε) (hm:0<mv) (hn:0<Fintype.card V)
    (hprotected:((Q.extendedVertices 1).card:ℝ)≤(b/8)*Fintype.card V):
    ε/2≤b/8 :=by
  have hinner:(ε/2)*(Fintype.card V:ℝ)≤(Q.extendedVertices 1).card:=by
    rw [Q.extendedVertices_eq (by have hh:=Q.length_pos;omega)]
    have hh:=(Q.consecutive_size_bounds hε hm Q.length_pos).1
    rw [Q.initial] at hh
    simp only [Finset.card_univ] at hh
    nlinarith
  have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  by_contra h
  have hp:0<(ε/2-b/8)*(Fintype.card V:ℝ):=mul_pos (by linarith) hn'
  nlinarith only [hinner,hprotected,hp]
end Oberwolfach
