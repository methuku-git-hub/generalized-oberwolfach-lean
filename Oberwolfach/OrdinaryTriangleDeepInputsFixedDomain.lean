module

public import Oberwolfach.OrdinaryDeepCoverLevelInputs
public import Oberwolfach.TwoComponentLower

@[expose] public section
/-! The checked deep-cover inputs also supply the full-parent domain
hypotheses for the combined triangle and reference-cut events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_deep_inputs_fixed_domain
    (Dmax d:ℕ) (α p ω a ε₀:ℝ) (P F:SimpleGraph V) (π:Equiv.Perm V)
    (J:Finset U) (pR pH D β:ℝ)
    (data:OrdinaryDeepCoverLevelInputs 2 Dmax d α p ω a ε₀ P F π J pR pH D β):
    ω*Fintype.card V≤(Fintype.card U:ℝ) ∧ Fintype.card U≤Fintype.card V ∧
    (∀v,(max (1/2) (cycleThreshold 3)+α)*Fintype.card V≤(P.degree v:ℝ)) ∧
    (∀v,(F.degree v:ℝ)≤Dmax) ∧ permutationConflictGraph π (3*d)≤F ∧
    (∀x l,0<l→l<2*d+1→(π^l) x≠x) ∧
    (Fintype.card V:ℝ)/2≤D ∧
    (∀v,|(P.degree v:ℝ)-D|≤ε₀*Fintype.card V) ∧
    pR*D=2*Fintype.card U*pH :=by
  have hU:((Finset.univ\J).card:ℝ)≤Fintype.card U:=by exact_mod_cast Finset.card_le_univ (Finset.univ\J)
  have hmax:max (1/2:ℝ) (cycleThreshold 3)=cycleThreshold 3:=max_eq_right (cycleThreshold_half_le (by omega))
  refine ⟨data.hub_lower.trans hU,data.hub_upper,?_,?_,data.conflict_contains,data.no_short,
    data.density_lower,?_,data.balance_mean⟩
  · intro v
    simpa only [hmax] using data.min_degree v
  · intro v
    exact_mod_cast data.conflict_degree v
  · intro v
    exact (data.approximate_regular v).trans (mul_le_mul_of_nonneg_right data.error_upper (by positivity))
end Oberwolfach
