module

public import Oberwolfach.LocalMatchingTestMassCeiling
public import Oberwolfach.LocalSpokeIncidenceSizes

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem local_matching_test_threshold_requires_local_size
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (v:Fin n) (H:Finset U)
    (Q:C→Finset S) (weight:C→ℝ) (a:ℝ):
    let I:=longLocalVertexSpokeIncidence S g v H
    (∀z∈I,(∑c,if z∈Q c then weight c else 0)≤1)→
    a*(n:ℝ)≤∑c,weight c*((Q c∩I).card:ℝ)→
    a*(n:ℝ)≤H.card:=by
  intro I hdegree hmass
  have hceil:=local_matching_test_mass_le_card I Q weight hdegree
  have hsize:(I.card:ℝ)≤H.card:=by exact_mod_cast long_local_vertex_spoke_incidence_card_le S g v H
  exact hmass.trans (hceil.trans hsize)
end Oberwolfach
