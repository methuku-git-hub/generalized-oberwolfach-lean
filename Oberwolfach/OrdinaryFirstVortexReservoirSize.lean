module

public import Oberwolfach.OrdinaryVortexInnerEventuallyLarge

@[expose] public section

/-! The first vortex level supplies both absorber-size hypotheses from the
single early bound on its contraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_first_vortex_reservoir_size
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hε:0<ε) (hm:0<mv) (hρ:initialIndexDensity U D≤1)
    (εabs εv:ℝ) (habs:ε≤εabs) (hv:ε≤εv):
    ((Q.extendedVertices 1).card:ℝ)≤εabs*Fintype.card V ∧
    ((Q.extendedIndices 1).card:ℝ)≤εabs*Fintype.card V ∧
    ((Q.extendedVertices 1).card:ℝ)≤εv*Fintype.card V ∧
    ((Q.extendedIndices 1).card:ℝ)≤εv*Fintype.card V :=by
  have hvertices:((Q.extendedVertices 1).card:ℝ)≤ε*Fintype.card V:=by
    rw [Q.extendedVertices_eq (by have hh:=Q.length_pos;omega)]
    have hh:=(Q.consecutive_size_bounds hε hm Q.length_pos).2
    rw [Q.initial] at hh
    simpa only [Finset.card_univ] using hh
  have hindexNat:=Q.extended_index_size_upper hreg hn hD hε.le hρ 1
  have hindex:2*((Q.extendedIndices 1).card:ℝ)≤(Q.extendedVertices 1).card:=by exact_mod_cast hindexNat
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have habs':ε*Fintype.card V≤εabs*Fintype.card V:=mul_le_mul_of_nonneg_right habs hn0
  have hv':ε*Fintype.card V≤εv*Fintype.card V:=mul_le_mul_of_nonneg_right hv hn0
  have hi0:(0:ℝ)≤(Q.extendedIndices 1).card:=by positivity
  exact ⟨hvertices.trans habs',by linarith,hvertices.trans hv',by linarith⟩
end Oberwolfach
