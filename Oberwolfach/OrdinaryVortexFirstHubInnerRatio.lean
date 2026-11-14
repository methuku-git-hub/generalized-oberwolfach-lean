module

public import Oberwolfach.OrdinaryVortexInnerEventuallyLarge

@[expose] public section

/-! Every set of hubs is at most a fixed multiple of the first inner
vertex level, with the multiplier chosen from the vortex contraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_first_hub_inner_ratio
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (hε:0<ε) (hm:0<mv) (hU:Fintype.card U≤Fintype.card V) (Hubs:Finset U):
    (Hubs.card:ℝ)≤(2/ε)*(Q.extendedVertices 1).card :=by
  have hinner:(ε/2)*(Fintype.card V:ℝ)≤(Q.extendedVertices 1).card:=by
    rw [Q.extendedVertices_eq (by have hh:=Q.length_pos;omega)]
    have hh:=(Q.consecutive_size_bounds hε hm Q.length_pos).1
    rw [Q.initial] at hh
    simp only [Finset.card_univ] at hh
    nlinarith
  have hHub:(Hubs.card:ℝ)≤Fintype.card V:=by
    exact_mod_cast (Finset.card_le_univ Hubs).trans hU
  have hscale:(Fintype.card V:ℝ)≤(2/ε)*(Q.extendedVertices 1).card:=by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hε).2
    nlinarith [hinner]
  exact hHub.trans hscale
end Oberwolfach
