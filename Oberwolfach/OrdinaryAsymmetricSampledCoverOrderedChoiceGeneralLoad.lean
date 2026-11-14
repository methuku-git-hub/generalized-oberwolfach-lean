module

public import Oberwolfach.OrdinaryLinearMatchingRootScaleGeneralLoad
public import Oberwolfach.OrdinaryLinearMatchingFineCoverCap
public import Oberwolfach.OrdinaryGeneralFinishAfterSampledCover

@[expose] public section
/-! Choose a quadratic protected root and then a matching capacity linear
in the vortex scale. Sampling and cover tolerances are selected afterward. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_sampled_cover_ordered_choice_general_load
    (m loadK:ℕ) (root edit eCoeff hCoeff εcap c:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff) (hεcap:0<εcap) (hc:0<c):
    ∃lam ε βe βh θmatch:ℝ,0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ lam=2*ε^2 ∧ 0<lam ∧ lam≤root ∧ lam≤1/4 ∧
      βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      lam≤βe/4 ∧ lam≤βh/2 ∧ 3*(((loadK:ℝ)+1)*lam)≤edit/4 ∧ lam*((m:ℝ)+1)≤edit/4 ∧
      θmatch=c*ε ∧ 0<θmatch ∧
    ∀rate pcap othercap:ℝ,0<rate→0<pcap→0<othercap→
    ∃ellCap k pbound:ℝ,ellCap=θmatch/64 ∧ 0<ellCap ∧ 0<k ∧ 0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→∃εsup cap δsample loadCap:ℝ,
      p≤1 ∧ p≤4*θmatch ∧ 20*Real.sqrt (2*p)≤θmatch/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧ 0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧
      (∀load ξ:ℝ,0≤load→load≤loadCap→0≤ξ→ξ≤load^2/160→
        max (18*load+3*(((loadK:ℝ)+1)*lam)) ((3*load+lam)*((m:ℝ)+1))≤ellCap ∧ 10*ξ≤cap) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θmatch*p/4 ∧ ν+η≤θmatch*p/4) ∧
    ∀ν:ℝ,0≤ν→ν≤cap→∃N:ℕ,∀n:ℕ,N≤n→
      2≤θmatch*p*n/4 ∧ ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤k^2*n ∧
      ∀(Lconf t η:ℝ),Lconf≤k^2*n→t≤ν*n→0≤η→η≤cap→
        ((n*Dmax*(m+1):ℕ):ℝ)/(K:ℝ)+
          (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
          (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*t ∧
        ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n:=by
  obtain ⟨ε,lam,βe,βh,θmatch,hε,hεcap,hε1,hlamEq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,hlevel,hθeq,hθ,hwide,hrootScale⟩:=
      ordinary_linear_matching_root_scale_general_load m loadK root edit eCoeff hCoeff εcap c hroot hedit he hh hεcap hc
  have hwide0:0≤((loadK:ℝ)+1)*lam:=by positivity
  obtain ⟨fineCap,hfine,hfine1,hcover⟩:=ordinary_linear_matching_fine_cover_cap m (((loadK:ℝ)+1)*lam) θmatch hwide0 hwide hθ hrootScale
  refine ⟨lam,ε,βe,βh,θmatch,hε,hεcap,hε1,hlamEq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,hlevel,hθeq,hθ,?_⟩
  intro rate pcap othercap hrate hpcap hother
  obtain ⟨ellCap,k,pbound,hellEq,hell,hk,hpbound,hpboundCap,hfinish⟩:=
    ordinary_general_finish_after_sampled_cover m (βe/2) 1 θmatch rate pcap othercap (by positivity)
      (by norm_num) hθ hrate hpcap hother
  have hellEq':ellCap=θmatch/64:=by simpa using hellEq
  refine ⟨ellCap,k,pbound,hellEq',hell,hk,hpbound,hpboundCap,?_⟩
  intro p hp hpbound'
  obtain ⟨εsup,cap,δsample,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hδsample,hrates,hcapacity⟩:=
    hfinish p hp hpbound'
  let loadCap:=min fineCap cap
  have hload:0<loadCap:=lt_min hfine hcap
  have hloadfine:loadCap≤fineCap:=min_le_left _ _
  have hloadcap:loadCap≤cap:=min_le_right _ _
  have hload1:loadCap≤1:=hloadfine.trans hfine1
  refine ⟨εsup,cap,δsample,loadCap,hp1,by simpa using hpθ,by simpa using hsqrt,hεsup,hεsupCap,
    hcap,hcapOther,hδsample,hload,hload1,?_,?_,?_⟩
  · intro load ξ hload0 hloadSmall hξ hξSmall
    obtain ⟨hcover1,_⟩:=hcover load ξ hload0 (hloadSmall.trans hloadfine) hξ hξSmall
    have hloadOne:load≤1:=hloadSmall.trans hload1
    have hsq:load^2≤load:=by nlinarith [mul_nonneg hload0 (sub_nonneg.mpr hloadOne)]
    have hξcap:10*ξ≤cap:=by nlinarith [hξSmall,hsq,hloadSmall,hloadcap]
    have hK0:(0:ℝ)≤loadK:=by positivity
    have hlamWide:lam≤((loadK:ℝ)+1)*lam:=by nlinarith [mul_nonneg hK0 hlam.le]
    have hright:(3*load+lam)*((m:ℝ)+1)≤(3*load+((loadK:ℝ)+1)*lam)*((m:ℝ)+1):=by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hsmall:max (18*load+3*(((loadK:ℝ)+1)*lam)) ((3*load+lam)*((m:ℝ)+1))≤θmatch/64:=by
      apply max_le
      · exact (le_max_left _ _).trans hcover1
      · exact hright.trans ((le_max_right _ _).trans hcover1)
    exact ⟨by simpa only [hellEq'] using hsmall,hξcap⟩
  · intro τ ν η ell hτ hν hη hell0 hτcap hνcap hηcap hellcap
    simpa using hrates τ ν η ell hτ hν hη hell0 hτcap hνcap hηcap hellcap
  · intro ν hν hνcap
    obtain ⟨N,hN⟩:=hcapacity ν hν hνcap
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨horder,K,Dmax,hK,hD,hDcap,hbounds⟩:=hN n hn
    refine ⟨by simpa using horder,K,Dmax,hK,hD,hDcap,?_⟩
    intro Lconf t η hL ht hη hηcap
    obtain ⟨hcomp,hcost⟩:=hbounds Lconf t η hL ht hη hηcap
    constructor
    · convert hcomp using 1 <;> congr 1 <;> ring
    · exact hcost
end Oberwolfach
