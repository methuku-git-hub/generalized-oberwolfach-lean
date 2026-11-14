module

public import Oberwolfach.MarkedInitialInnerVertexBound

@[expose] public section
/-! Both the initial inner vertex and hub sets have the vortex size bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_initial_inner_hub_bound
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq U]
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (hε:0≤ε) (hU:Fintype.card U≤Fintype.card V):
    ((Q.extendedIndices 1).card:ℝ)≤ε*Fintype.card V:=by
  have hstep:((Q.extendedIndices 1).card:ℝ)≤ε*(Fintype.card U:ℝ):=by
    have hh:=(Q.extended_successor_size_bounds hε 0).2
    simpa only [Nat.zero_add,Q.extendedIndices_eq (Nat.zero_le _),Q.indices_initial,Finset.card_univ] using hh
  have hcard:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hU
  exact hstep.trans (mul_le_mul_of_nonneg_left hcard hε)
end Oberwolfach
