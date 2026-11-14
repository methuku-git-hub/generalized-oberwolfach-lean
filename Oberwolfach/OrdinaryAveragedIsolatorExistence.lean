module

public import Oberwolfach.AveragedRimIsolator

@[expose] public section

/-! The actual rim isolator supplied by the admissible induced-subgraph
families, with its coefficient bound and its effect on each spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_averaged_isolator_exists (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V U : Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (P Q F : SimpleGraph V) (H : V → U → Prop) (k : ℕ),N≤k →
      ∀ θ : ℝ,cycleThreshold r≤θ → ∀ γ : ℝ,0<γ → 0<Fintype.card V →
      ∀ x y,P.Adj x y →
      γ*(Fintype.card V:ℝ)^(k-1)≤
        (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ) →
      ∃ I : OrdinaryWheel Q F H r → ℝ,
        (∀ a b,ordinaryRimLoad I a b=if (SimpleGraph.edge x y).Adj a b then 1 else 0) ∧
        (∀ D,|I D|≤1/(γ*(Fintype.card V:ℝ)^
          (((ordinaryWheelRim D).support.toFinset∪{x,y}).card-1))) ∧
        (∀ z h,|ordinarySpokeLoad I z h|≤
          (if z=x ∨ z=y then (1:ℝ) else 0)/(2*γ*Fintype.card V)) := by
  obtain ⟨N,hN⟩ := ordinary_isolator_configuration_weights r hr α hα
  refine ⟨max N (r+2),?_⟩
  intro V U _ _ _ _ P Q F H k hk θ hθ γ hγ hn x y hxy hcount
  have hkN : N≤k := (le_max_left _ _).trans hk
  have hkr : r+2≤k := (le_max_right _ _).trans hk
  have hh := hN V U P Q F H k hkN θ hθ x y hxy
  choose ψ hb hs he hv using hh
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hpos : 0<Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y) := by
    have hp : (0:ℝ)<γ*(Fintype.card V:ℝ)^(k-1) := by positivity
    exact_mod_cast hp.trans_le hcount
  refine ⟨finiteSignedAverage ψ,(averaged_rim_isolator_loads ψ hpos he hv).1,?_,?_⟩
  · exact averaged_rim_isolator_coefficient_bound hr hkr ψ hb hs γ hγ hn hcount
  · exact averaged_rim_isolator_spoke_bound (by omega) hxy.ne ψ he hv γ hγ hn hcount

end Oberwolfach
