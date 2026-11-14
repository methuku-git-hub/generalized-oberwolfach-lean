module

public import Oberwolfach.EndpointParentWeightSampleInputs
public import Oberwolfach.EndpointParentWeights

@[expose] public section
/-! Choose the fractional parent matching before the sampled host and any
subsequent bounded symmetric edit, uniformly over all such later choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_parent_weights_before_edited_sample (P:SimpleGraph V) (A:Finset V) (x:V)
    (hn:32≤A.card)
    (hdeg:∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    ∃weight:Sym2 V→ℝ,
      ∀(R₀ R H₀ H F:SimpleGraph V) (B:Finset V) (κ p q s L Ledit δ ξ:ℝ),
        EndpointParentWeightSampleInputs P R₀ R H₀ H F A B x weight κ p q s L Ledit δ ξ→
        EndpointParentWeightSampleConclusion R H F A B x weight κ p q s L Ledit δ ξ := by
  obtain ⟨weight,hweight,hsum,hzero,hpositive⟩:=endpoint_parent_matching_exists P A x hn hdeg
  refine ⟨weight,?_⟩
  intro R₀ R H₀ H F B κ p q s L Ledit δ ξ inp
  have ha:0<(A.card:ℝ):=by exact_mod_cast (show 0<A.card by omega)
  exact endpoint_fixed_weights_after_symmetric_edits P R₀ R H₀ H F A B x
    inp.disjoint inp.rim_sub inp.conflict_free_index κ p q s (1/30) 40 L Ledit δ ξ
    ha inp.kappa_pos inp.p_pos (by norm_num) (by norm_num) inp.conflict_nonneg inp.edit_nonneg
    inp.balance_nonneg inp.index_lower inp.index_upper inp.rim_lower inp.rim_upper inp.spoke_lower
    inp.spoke_upper inp.conflict_degree weight hweight hsum (fun v _ w _=>hzero v w)
    (hpositive F) inp.parent_balance inp.row_potential inp.index_potential inp.rim_edit inp.spoke_edit
end Oberwolfach
