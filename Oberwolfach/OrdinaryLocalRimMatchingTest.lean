module

public import Oberwolfach.OrdinaryLocalRimIncidence
public import Oberwolfach.LocalMatchingTestDefect

@[expose] public section
/-! A matching test on each local rim row controls the uncovered degree
at the scale of the protected set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_local_rim_matching_test
    {V U W C:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype C]
    [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq C]
    (φ:W↪Sym2 V⊕(V×U)) (Inner:Finset V) (M:Finset C) (Q:C→Finset W) (weight:C→ℝ) (ε γ:ℝ)
    (hγ:0≤γ) (hγ1:γ≤1) (hε:0≤ε)
    (hdis:∀c∈M,∀d∈M,c≠d→Disjoint (Q c) (Q d))
    (hmass:∀x,let I:=ordinaryLocalRimIncidence φ x Inner;
      (1-ε)*(I.card:ℝ)≤∑c,weight c*((Q c∩I).card:ℝ))
    (htest:∀x,let I:=ordinaryLocalRimIncidence φ x Inner;
      (1-γ)*(∑c,weight c*((Q c∩I).card:ℝ))≤∑c∈M,((Q c∩I).card:ℝ)):
    ∀x,((spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner).degree x:ℝ)≤
      (ε+γ)*Inner.card :=by
  intro x
  let I:=ordinaryLocalRimIncidence φ x Inner
  have hdef:=local_matching_test_defect I M Q weight ε γ hγ hγ1 hε hdis (hmass x) (htest x)
  have hcard:((I.card:ℕ):ℝ)≤Inner.card:=by exact_mod_cast ordinary_local_rim_incidence_card_le φ x Inner
  have hdeg:((spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner).degree x:ℝ)≤
      (I\M.biUnion Q).card:=by exact_mod_cast ordinary_local_rim_residual_degree_le_uncovered φ (M.biUnion Q) x Inner
  exact hdeg.trans (hdef.trans (mul_le_mul_of_nonneg_left hcard (by linarith)))
end Oberwolfach
