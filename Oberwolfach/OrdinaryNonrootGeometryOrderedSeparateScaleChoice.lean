module

public import Oberwolfach.OrdinaryNonrootGeometryStatic

@[expose] public section
/-! Choose the static nonroot geometry and fresh-reserve scales before the
finite host, from the positive parent degree and weight margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_geometry_ordered_separate_scale_choice
    (r k:ℕ) (ω βparent b B εparent gap cap:ℝ)
    (hk:4≤k) (hω:0<ω) (hβ:0<βparent) (hb:0<b) (hB:0≤B)
    (hgap:0<gap) (hcap:0<cap):
    ∃β ξ ζ edit:ℝ,0<β ∧ β=βparent/2 ∧ 0<ξ ∧ 0<ζ ∧ 0<edit ∧ ξ≤cap ∧ ζ≤cap ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (X:Finset V) (Z:Finset U) (f binner c ell:ℝ),
      0<Fintype.card V→0<Fintype.card U→ω*Fintype.card V≤Fintype.card U→Fintype.card U≤Fintype.card V→
      (X.card:ℝ)≤ξ*Fintype.card V→(Z.card:ℝ)≤ξ*Fintype.card V→(Z.card:ℝ)≤ξ*Fintype.card U→
      0≤f→0≤binner→0≤c→0≤ell→
      f≤γ*Fintype.card V→binner≤γ*Fintype.card V→c≤γ*Fintype.card V→ell≤edit*Fintype.card V→
      OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent (εparent+gap) η ξ ζ p eps f binner c X Z ∧
      ell+(p+eps)*Fintype.card (V⊕U)≤ζ*Fintype.card V ∧
      ell+(p+eps)*Fintype.card (V⊕U)≤ζ*Fintype.card U :=by
  let R:ℝ:=(r:ℝ)^4
  have hR:0≤R:=by dsimp [R];positivity
  let q:ℝ:=min (1/2) (min (βparent/(100*(R+1))) (min (gap/(100*(R*(B+1)+1))) (cap/2)))
  have hq:0<q:=by dsimp [q];positivity
  let w:ℝ:=min 1 ω
  have hw:0<w:=lt_min (by norm_num) hω
  have hw1:w≤1:=min_le_left _ _
  have hwω:w≤ω:=min_le_right _ _
  have hqone:q≤1/2:=min_le_left _ _
  have hqcap:q≤cap/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨βparent/2,q,q,q*w/8,by positivity,rfl,hq,hq,by positivity,by linarith,by linarith,?_⟩
  intro pcap hpcap
  let p:ℝ:=min (q*w/16) (pcap/2)
  have hp:0<p:=by dsimp [p];positivity
  have hpq:p≤q*w/16:=min_le_left _ _
  have hpc:p≤pcap:=by have hh:=min_le_right (q*w/16) (pcap/2);dsimp [p];linarith
  have hp1:p≤1:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hw1)]
  refine ⟨p,hp,hp1,hpc,?_⟩
  intro η hη
  let t:ℝ:=min p (η/100)
  let g:ℝ:=min (q*w/8) (η/100)
  have ht:0<t:=by dsimp [t];positivity
  have hg:0<g:=by dsimp [g];positivity
  have hqβ:q≤βparent/(100*(R+1)):=le_trans (min_le_right _ _) (min_le_left _ _)
  have hqgap:q≤gap/(100*(R*(B+1)+1)):=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hqβ':q*(R+1)≤βparent/100:=by
    have hh:0<100*(R+1):=by positivity
    have h: q*(100*(R+1))≤βparent:=(le_div_iff₀ hh).mp hqβ
    nlinarith only [h]
  have hqgap':q*(R*(B+1)+1)≤gap/100:=by
    have hh:0<100*(R*(B+1)+1):=by positivity
    have h:q*(100*(R*(B+1)+1))≤gap:=(le_div_iff₀ hh).mp hqgap
    nlinarith only [h]
  have htq:t≤q*w/16:=(min_le_left p (η/100)).trans hpq
  have htη:t≤η/100:=min_le_right _ _
  have hgq:g≤q*w/8:=min_le_left _ _
  have hgη:g≤η/100:=min_le_right _ _
  have htw:t≤q*w/16:=htq
  have htone:t≤1:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hw1)]
  refine ⟨t,g,ht,htone,hg,?_⟩
  intro V U _ _ _ _ X Z f binner c ell hn hu hU hUn hX hZV hZU hf hbinner hc hell hf' hbinner' hc' hell'
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have huR:(0:ℝ)<Fintype.card U:=by exact_mod_cast hu
  have hUnR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hUn
  have hsum:(Fintype.card (V⊕U):ℝ)=(Fintype.card V:ℝ)+Fintype.card U:=by simp
  have hN:(Fintype.card (V⊕U):ℝ)≤2*Fintype.card V:=by rw [hsum];linarith
  have hqR:0≤q*R:=mul_nonneg hq.le hR
  have hqRB:0≤q*R*B:=mul_nonneg hqR hB
  have hcoef:βparent/2+q+q≤βparent:=by nlinarith only [hqβ',hqR,hq.le]
  have hisol:8*(q+q)≤βparent-βparent/2:=by nlinarith only [hqβ',hqR,hq.le]
  have htrans:5*R*(q+q)≤βparent-βparent/2:=by nlinarith only [hqβ',hqR,hq.le]
  have hweight:εparent+8*R*B*(q+q)≤εparent+gap:=by nlinarith only [hqgap',hqR,hq.le,hqRB]
  have hpw1:p≤q/16:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hw1)]
  have hpwω:p≤q*ω/16:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hwω)]
  have htw1:t≤q/16:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hw1)]
  have htwω:t≤q*ω/16:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hwω)]
  have hgw1:q*w/8≤q/8:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hw1)]
  have hgwω:q*w/8≤q*ω/8:=by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hwω)]
  have hps1:p+t≤q/8:=by linarith
  have hpsω:p+t≤q*ω/8:=by linarith
  have hresV:(p+t)*(Fintype.card (V⊕U):ℝ)≤q*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_left hN (show 0≤p+t by positivity)
    have hh':=mul_le_mul_of_nonneg_right hps1 hnR.le
    nlinarith only [hh,hh',mul_nonneg hq.le hnR.le]
  have hresU:(p+t)*(Fintype.card (V⊕U):ℝ)≤q*Fintype.card U:=by
    have hh:=mul_le_mul_of_nonneg_left hN (show 0≤p+t by positivity)
    have hh':=mul_le_mul_of_nonneg_right hpsω hnR.le
    have hh'':=mul_le_mul_of_nonneg_left hU hq.le
    nlinarith only [hh,hh',hh'',mul_nonneg (mul_nonneg hq.le hω.le) hnR.le]
  have hscaleV:ell+(p+t)*(Fintype.card (V⊕U):ℝ)≤q*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_left hN (show 0≤p+t by positivity)
    have hh':=mul_le_mul_of_nonneg_right hps1 hnR.le
    have hh'':=mul_le_mul_of_nonneg_right hgw1 hnR.le
    nlinarith only [hh,hh',hh'',hell',mul_nonneg hq.le hnR.le]
  have hscaleU:ell+(p+t)*(Fintype.card (V⊕U):ℝ)≤q*Fintype.card U:=by
    have hh:=mul_le_mul_of_nonneg_left hN (show 0≤p+t by positivity)
    have hh':=mul_le_mul_of_nonneg_right hpsω hnR.le
    have hh'':=mul_le_mul_of_nonneg_right hgwω hnR.le
    have hh''':=mul_le_mul_of_nonneg_left hU hq.le
    nlinarith only [hh,hh',hh'',hh''',hell',mul_nonneg (mul_nonneg hq.le hω.le) hnR.le]
  have hmax:0≤max (f+binner) c:=le_trans (by positivity : (0:ℝ)≤f+binner) (le_max_left _ _)
  have hmaxcap:max (f+binner) c≤2*g*Fintype.card V:=by
    apply max_le <;> nlinarith only [hf',hbinner',hc',hg,hnR]
  have hpmax:p*max (f+binner) c≤2*g*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_right hp1 hmax
    nlinarith only [hh,hmaxcap]
  have hbalance:f+binner+p*max (f+binner) c+3*t*Fintype.card (V⊕U)≤η*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_left hN ht.le
    have hh':=mul_le_mul_of_nonneg_right hgη hnR.le
    have hh'':=mul_le_mul_of_nonneg_right htη hnR.le
    nlinarith only [hf',hbinner',hpmax,hh,hh',hh'',mul_nonneg hη.le hnR.le]
  refine ⟨⟨hn,hu,hU,hUn,hq.le,hq.le,hp.le,hb,hB,hk,hX,hZV,hZU,hresV,hresU,hcoef,?_,?_,?_,hbalance⟩,hscaleV,hscaleU⟩
  · nlinarith only [mul_le_mul_of_nonneg_right hisol hnR.le]
  · dsimp [R] at htrans
    nlinarith only [mul_le_mul_of_nonneg_right htrans hnR.le]
  · simpa only [R] using hweight
end Oberwolfach
