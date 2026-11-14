module

public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Actual vertex-domain and edge deletion losses for sampled endpoint
degrees. Parent degrees and the retention probability are kept fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

theorem intersection_card_change_bound (A B S:Finset V):
    |((A∩S).card:ℝ)-(B∩S).card|≤(changed A B).card:=by
  apply (card_difference_le_changed _ _).trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at hv ⊢
  tauto

theorem deleted_intersection_card_change_bound (A B S E:Finset V):
    |(((A∩S)\E).card:ℝ)-(B∩S).card|≤(changed A B).card+E.card:=by
  have hdel:|(((A∩S)\E).card:ℝ)-(A∩S).card|≤E.card:=by
    have hc:=Finset.card_le_card_sdiff_add_card (s:=A∩S) (t:=E)
    have hu:=Finset.card_le_card (Finset.sdiff_subset (s:=A∩S) (t:=E))
    have hc':((A∩S).card:ℝ)≤((A∩S)\E).card+E.card:=by exact_mod_cast hc
    have hu':(((A∩S)\E).card:ℝ)≤(A∩S).card:=by exact_mod_cast hu
    apply abs_le.mpr;constructor <;> linarith
  have hh:=intersection_card_change_bound A B S
  have ht:=abs_sub_le (((A∩S)\E).card:ℝ) ((A∩S).card:ℝ) ((B∩S).card:ℝ)
  linarith only [hdel,hh,ht]

theorem sampled_domain_degree_after_changes (A A' A'' S E:Finset V) (p ρ η:ℝ)
    (hp:0≤p) (hp1:p≤1) (hρ:0≤ρ) (hη:0≤η) (hη1:η≤1/4)
    (hparent:|((A∩S).card:ℝ)-p*A.card|≤η*A.card)
    (hsample:|((A'∩S).card:ℝ)-ρ*(A∩S).card|≤η*(ρ*A.card))
    (hsize:|((A'').card:ℝ)-ρ*A.card|≤2*η*(ρ*A.card))
    (hchange:((changed A'' A').card:ℝ)≤η*(ρ*A.card))
    (hedge:(E.card:ℝ)≤η*(ρ*A.card)):
    |(((A''∩S)\E).card:ℝ)-p*A''.card|≤12*η*A''.card:=by
  have hn:0≤(A.card:ℝ):=Nat.cast_nonneg _
  have hscale:0≤ρ*A.card:=mul_nonneg hρ hn
  have hdiff:|(((A''∩S)\E).card:ℝ)-(A'∩S).card|≤2*η*(ρ*A.card):=by
    have hh:=deleted_intersection_card_change_bound A'' A' S E
    linarith only [hh,hchange,hedge]
  have hpar:|ρ*(A∩S).card-p*(ρ*A.card)|≤η*(ρ*A.card):=by
    have hh:=mul_le_mul_of_nonneg_left hparent hρ
    have he:ρ*((A∩S).card-p*A.card)=ρ*(A∩S).card-p*(ρ*A.card):=by ring
    rw [←abs_of_nonneg hρ,←abs_mul,he,abs_of_nonneg hρ] at hh
    nlinarith only [hh]
  have htarget:|p*(ρ*A.card)-p*A''.card|≤2*η*(ρ*A.card):=by
    have hh:=mul_le_mul_of_nonneg_left hsize hp
    have he:p*((A''.card:ℝ)-ρ*A.card)=p*A''.card-p*(ρ*A.card):=by ring
    rw [←abs_of_nonneg hp,←abs_mul,he,abs_sub_comm,abs_of_nonneg hp] at hh
    have hs:=mul_le_mul_of_nonneg_right hp1 (show 0≤2*η*(ρ*A.card) by positivity)
    linarith only [hh,hs]
  have htotal:|(((A''∩S)\E).card:ℝ)-p*A''.card|≤6*η*(ρ*A.card):=by
    have h1:=abs_sub_le (((A''∩S)\E).card:ℝ) ((A'∩S).card:ℝ) (p*A''.card)
    have h2:=abs_sub_le ((A'∩S).card:ℝ) (ρ*(A∩S).card) (p*A''.card)
    have h3:=abs_sub_le (ρ*(A∩S).card) (p*(ρ*A.card)) (p*A''.card)
    linarith only [hdiff,hsample,hpar,htarget,h1,h2,h3]
  have hlo:ρ*A.card≤2*(A''.card:ℝ):=by
    have hh:=(abs_le.mp hsize).1
    have hsmall:=mul_le_mul_of_nonneg_right hη1 hscale
    nlinarith only [hh,hsmall]
  have hh:=mul_le_mul_of_nonneg_left hlo (show 0≤6*η by positivity)
  nlinarith only [htotal,hh]


theorem sampled_domain_size_after_changes (A A' A'':Finset V) (ρ η:ℝ)
    (hρ:0≤ρ) (hη:0≤η) (hη1:η≤1/4)
    (hsample:|((A').card:ℝ)-ρ*A.card|≤η*(ρ*A.card))
    (hchange:((changed A'' A').card:ℝ)≤η*(ρ*A.card)):
    |((A'').card:ℝ)-ρ*A.card|≤2*η*(ρ*A.card) ∧
      ρ*A.card/2≤(A''.card:ℝ) ∧ (A''.card:ℝ)≤2*(ρ*A.card):=by
  have hdiff:|((A'').card:ℝ)-A'.card|≤η*(ρ*A.card):=
    (card_difference_le_changed A'' A').trans hchange
  have ht:=abs_sub_le (A''.card:ℝ) (A'.card:ℝ) (ρ*A.card)
  have hh:|((A'').card:ℝ)-ρ*A.card|≤2*η*(ρ*A.card):=by linarith only [hdiff,hsample,ht]
  have hn:0≤ρ*A.card:=by positivity
  have hm:=mul_le_mul_of_nonneg_right hη1 hn
  refine ⟨hh,?_,?_⟩
  · have hlo:=(abs_le.mp hh).1;nlinarith only [hlo,hm]
  · have hhi:=(abs_le.mp hh).2;nlinarith only [hhi,hm,hn]

theorem sampled_domain_codegree_upper (A A' A'' S:Finset V) (p ρ η:ℝ)
    (hp:0≤p) (hp1:p≤1) (hρ:0≤ρ) (hη:0≤η) (hη1:η≤1/4)
    (hparent:((A∩S).card:ℝ)≤(p^2+η)*A.card)
    (hsample:|((A'∩S).card:ℝ)-ρ*(A∩S).card|≤η*(ρ*A.card))
    (hsize:|((A'').card:ℝ)-ρ*A.card|≤2*η*(ρ*A.card))
    (hchange:((changed A'' A').card:ℝ)≤η*(ρ*A.card)):
    ((A''∩S).card:ℝ)≤(p^2+10*η)*A''.card:=by
  have hn:0≤ρ*A.card:=by positivity
  have hdiff:|((A''∩S).card:ℝ)-(A'∩S).card|≤η*(ρ*A.card):=
    (intersection_card_change_bound A'' A' S).trans hchange
  have hd:=(abs_le.mp hdiff).2
  have hs:=(abs_le.mp hsample).2
  have hpard:=mul_le_mul_of_nonneg_left hparent hρ
  have hpre:((A''∩S).card:ℝ)≤p^2*(ρ*A.card)+3*η*(ρ*A.card):=by
    nlinarith only [hd,hs,hpard]
  have hsz:=(abs_le.mp hsize).1
  have hp2:p^2≤1:=by nlinarith
  have hshift:=mul_le_mul_of_nonneg_left hsz (sq_nonneg p)
  have herr:=mul_le_mul_of_nonneg_right hp2 (show 0≤2*η*(ρ*A.card) by positivity)
  have hpre':((A''∩S).card:ℝ)≤p^2*A''.card+5*η*(ρ*A.card):=by
    nlinarith only [hpre,hshift,herr]
  have hsmall:=mul_le_mul_of_nonneg_right hη1 hn
  have hlo:ρ*A.card≤2*(A''.card:ℝ):=by nlinarith only [hsz,hsmall]
  have hh:=mul_le_mul_of_nonneg_left hlo (show 0≤5*η by positivity)
  nlinarith only [hpre',hh]

end Oberwolfach
