module

public import Oberwolfach.OrdinaryLocalRimMatchingTest
public import Oberwolfach.OrdinaryUncoveredRimMatchingTransfer

@[expose] public section
/-! Local weighted matching tests bound unmatched nonreference edges in the
protected region, with a separate bound for exceptional sampled edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_local_uncovered_from_coverage
    {V U W C:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype C]
    [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq C]
    (φ:W↪Sym2 V⊕(V×U)) (Inner:Finset V) (M:Finset C) (Q:C→Finset W) (κ δ:ℝ)
    (hrow:∀x,(((ordinaryLocalRimIncidence φ x Inner)\M.biUnion Q).card:ℝ)≤κ)
    (Sample Reference Used Except:SimpleGraph V)
    (hExcept:∀v,((spanningRestriction Except Inner).degree v:ℝ)≤δ)
    (hactive:Sample\Reference≤physicalRimResidualGraph φ ∅⊔Except)
    (hpacked:physicalRimCoveredGraph φ (M.biUnion Q)≤Used):
    ∀v,((spanningRestriction ((Sample\Reference)\Used) Inner).degree v:ℝ)≤κ+δ :=by
  have hsub:spanningRestriction ((Sample\Reference)\Used) Inner≤
      spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner⊔spanningRestriction Except Inner:=by
    intro x y h
    have hh:=(spanningRestriction_adj ((Sample\Reference)\Used) Inner x y).mp h
    rcases hactive hh.1.1 with ha|he
    · left
      apply (spanningRestriction_adj (physicalRimResidualGraph φ (M.biUnion Q)) Inner x y).mpr
      refine ⟨⟨ha.1,?_⟩,hh.2.1,hh.2.2⟩
      obtain ⟨z,_,hz⟩:=ha.2
      refine ⟨z,?_,hz⟩
      intro hcov
      exact hh.1.2 (hpacked ⟨ha.1,z,hcov,hz⟩)
    · exact Or.inr ((spanningRestriction_adj Except Inner x y).mpr ⟨he,hh.2.1,hh.2.2⟩)
  have hlocal:∀x,((spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner).degree x:ℝ)≤κ:=by
    intro x
    have hh:((spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner).degree x:ℝ)≤
        ((ordinaryLocalRimIncidence φ x Inner\M.biUnion Q).card:ℝ):=by
      exact_mod_cast ordinary_local_rim_residual_degree_le_uncovered φ (M.biUnion Q) x Inner
    exact hh.trans (hrow x)
  intro v
  have hdeg:((spanningRestriction ((Sample\Reference)\Used) Inner).degree v:ℝ)≤
      ((spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner⊔spanningRestriction Except Inner).degree v:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub
  have hsum:=graph_degree_sup_le (spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner) (spanningRestriction Except Inner) v
  have hsum':((spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner⊔spanningRestriction Except Inner).degree v:ℝ)≤
      (spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner).degree v+(spanningRestriction Except Inner).degree v:=by
    have hh:(spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner⊔spanningRestriction Except Inner).degree v≤
        (spanningRestriction (physicalRimResidualGraph φ (M.biUnion Q)) Inner).degree v+(spanningRestriction Except Inner).degree v:=by
      convert hsum using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  linarith [hlocal v,hExcept v]
end Oberwolfach
