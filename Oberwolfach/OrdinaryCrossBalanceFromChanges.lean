module

public import Oberwolfach.SampledDomainDegreeChanges

@[expose] public section
/-! The actual edited cross profile stays balanced when rim and spoke
profiles and their parent density target are all controlled. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_cross_balance_from_changes
    {V U:Type} [DecidableEq V] [DecidableEq U]
    (A A₀ P I:Finset V) (B B₀ J:Finset U) (pR pH tR tH e L:ℝ)
    (hr:|((A₀∩I).card:ℝ)-pR*(P∩I).card|≤tR)
    (hs:|((B₀∩J).card:ℝ)-pH*J.card|≤tH)
    (hparent:|pR*(P∩I).card-2*pH*J.card|≤e)
    (hAr:((changed A A₀).card:ℝ)≤L) (hBs:((changed B B₀).card:ℝ)≤L):
    |((A∩I).card:ℝ)-2*(B∩J).card|≤e+tR+2*tH+3*L:=by
  have h1:|((A∩I).card:ℝ)-(A₀∩I).card|≤L:=(intersection_card_change_bound A A₀ I).trans hAr
  have h2:|((B∩J).card:ℝ)-(B₀∩J).card|≤L:=(intersection_card_change_bound B B₀ J).trans hBs
  have h1':=abs_le.mp h1
  have h2':=abs_le.mp h2
  have hr':=abs_le.mp hr
  have hs':=abs_le.mp hs
  have hp':=abs_le.mp hparent
  apply abs_le.mpr
  constructor <;> linarith only [h1'.1,h1'.2,h2'.1,h2'.2,hr'.1,hr'.2,hs'.1,hs'.2,hp'.1,hp'.2]
end Oberwolfach
