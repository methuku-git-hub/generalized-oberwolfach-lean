module

public import Oberwolfach.SampledDomainDegreeChanges

@[expose] public section
/-! A balanced cross profile changes by at most the three row edit costs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cross_balance_change
    {V U:Type} [DecidableEq V] [DecidableEq U]
    (A A₀ I:Finset V) (B B₀ J:Finset U) (b L:ℝ)
    (hbase:|((A₀∩I).card:ℝ)-2*(B₀∩J).card|≤b)
    (hr:((changed A A₀).card:ℝ)≤L)
    (hs:((changed B B₀).card:ℝ)≤L):
    |((A∩I).card:ℝ)-2*(B∩J).card|≤b+3*L:=by
  have h1:=abs_le.mp ((intersection_card_change_bound A A₀ I).trans hr)
  have h2:=abs_le.mp ((intersection_card_change_bound B B₀ J).trans hs)
  have hb:=abs_le.mp hbase
  apply abs_le.mpr
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,hb.1,hb.2]
end Oberwolfach
