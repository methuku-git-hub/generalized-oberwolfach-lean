module

public import Oberwolfach.LocalSpokeIncidenceSizes

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_local_vertex_spoke_defect_small_from_matching_test
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (v:Fin n) (H:Finset U)
    (M:Finset C) (Q:C→Finset S) (weight:C→ℝ) (ε γ:ℝ)
    (hγ:0≤γ) (hγ1:γ≤1) (hε:0≤ε)
    (hdis:∀c∈M,∀d∈M,c≠d→Disjoint (Q c) (Q d)):
    let I:=longLocalVertexSpokeIncidence S g v H
    (1-ε)*(I.card:ℝ)≤∑c,weight c*((Q c∩I).card:ℝ)→
    (1-γ)*(∑c,weight c*((Q c∩I).card:ℝ))≤∑c∈M,((Q c∩I).card:ℝ)→
    ((longLocalVertexSpokeDefects S (M.biUnion Q) g v H).card:ℝ)≤(ε+γ)*H.card:=by
  intro I hmass htest
  have h:=long_local_vertex_spoke_defect_from_matching_test S g v H M Q weight ε γ hγ hγ1 hε hdis hmass htest
  have hi:(I.card:ℝ)≤H.card:=by exact_mod_cast long_local_vertex_spoke_incidence_card_le S g v H
  exact h.trans (mul_le_mul_of_nonneg_left hi (by linarith))

theorem long_local_hub_spoke_defect_small_from_matching_test
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (w:U) (A:Finset (Fin n))
    (M:Finset C) (Q:C→Finset S) (weight:C→ℝ) (ε γ:ℝ)
    (hγ:0≤γ) (hγ1:γ≤1) (hε:0≤ε)
    (hdis:∀c∈M,∀d∈M,c≠d→Disjoint (Q c) (Q d)):
    let I:=longLocalHubSpokeIncidence S g w A
    (1-ε)*(I.card:ℝ)≤∑c,weight c*((Q c∩I).card:ℝ)→
    (1-γ)*(∑c,weight c*((Q c∩I).card:ℝ))≤∑c∈M,((Q c∩I).card:ℝ)→
    ((longLocalHubSpokeDefects S (M.biUnion Q) g w A).card:ℝ)≤(ε+γ)*A.card:=by
  intro I hmass htest
  have h:=long_local_hub_spoke_defect_from_matching_test S g w A M Q weight ε γ hγ hγ1 hε hdis hmass htest
  have hi:(I.card:ℝ)≤A.card:=by exact_mod_cast long_local_hub_spoke_incidence_card_le S g w A
  exact h.trans (mul_le_mul_of_nonneg_left hi (by linarith))
end Oberwolfach
