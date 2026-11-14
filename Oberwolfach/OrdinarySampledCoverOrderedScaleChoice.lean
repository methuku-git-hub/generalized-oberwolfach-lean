module

public import Oberwolfach.OrdinaryGeneralFinishAfterSampledCover
public import Oberwolfach.OrdinarySharpLinearRootScaleBeforeSampling
public import Oberwolfach.OrdinaryFineCoverRateCapChoice

@[expose] public section
/-! The root size is selected before the sampling density.  The root-cover
load enters the matching budget only through its sampled fraction; the
profile rate may be selected after the vortex and before the density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampled_cover_ordered_scale_choice
    (m:ℕ) (root edit eCoeff hCoeff εcap κ ζ:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff) (hεcap:0<εcap)
    (hκ:0<κ) (hζ:0<ζ):
    ∃lam ε βe βh:ℝ,0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ lam=2*ε^2 ∧ 0<lam ∧ lam≤root ∧ lam≤1/4 ∧
      βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      lam≤βe/4 ∧ lam≤βh/2 ∧ 3*lam≤edit/4 ∧ lam*((m:ℝ)+1)≤edit/4 ∧
    ∀rate pcap othercap:ℝ,0<rate→0<pcap→0<othercap→
    ∃ellCap k pbound:ℝ,ellCap=ζ*κ/64 ∧ 0<ellCap ∧ 0<k ∧ 0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→∃εsup cap δsample loadCap:ℝ,
      p≤1 ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧ 0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧
      (∀load ξ:ℝ,0≤load→load≤loadCap→0≤ξ→ξ≤load^2/160→
        max (18*load+3*lam) ((3*load+lam)*((m:ℝ)+1))≤ellCap ∧ 10*ξ≤cap) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤ζ*κ*p/4 ∧ ν+η≤ζ*κ*p/4) ∧
    ∀ν:ℝ,0≤ν→ν≤cap→∃N:ℕ,∀n:ℕ,N≤n→
      2≤ζ*κ*p*n/4 ∧ ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤k^2*n ∧
      ∀(Lconf t η:ℝ),Lconf≤k^2*n→t≤ν*n→0≤η→η≤cap→
        ((n*Dmax*(m+1):ℕ):ℝ)/(K:ℝ)+
          (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
          (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*t ∧
        ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n :=by
  let target:=ζ*κ/64
  have htarget:0<target:=by dsimp [target];positivity
  obtain ⟨rootCap,loadLimit,hrootCap,hloadLimit,hcover⟩:=ordinary_fine_cover_rate_cap_choice m target htarget
  let root':=min root rootCap
  have hroot':0<root':=lt_min hroot hrootCap
  obtain ⟨ε,lam,βe,βh,hε,hεcap,hε1,hlameq,hlam,hlamcap,hlam1,hβeEq,hβhEq,hβe,hβh,hlame,hlamh,hrow,hlevel⟩:=
    ordinary_sharp_linear_root_scale_before_sampling m root' edit eCoeff hCoeff εcap hroot' hedit he hh hεcap
  have hlamroot:lam≤root:=hlamcap.trans (min_le_left _ _)
  have hlamcover:lam≤rootCap:=hlamcap.trans (min_le_right _ _)
  refine ⟨lam,ε,βe,βh,hε,hεcap,hε1,hlameq,hlam,hlamroot,hlam1,hβeEq,hβhEq,hβe,hβh,hlame,hlamh,hrow,hlevel,?_⟩
  intro rate pcap othercap hrate hpcap hother
  obtain ⟨ellCap,k,pbound,hellEq,hell,hk,hpbound,hpboundCap,hfinish⟩:=
    ordinary_general_finish_after_sampled_cover m (βe/2) κ ζ rate pcap othercap (by positivity) hκ hζ hrate hpcap hother
  refine ⟨ellCap,k,pbound,hellEq,hell,hk,hpbound,hpboundCap,?_⟩
  intro p hp hpbound'
  obtain ⟨εsup,cap,δsample,hp1,hpκ,hsqrt,hεsup,hεsupcap,hcap,hcapOther,hδsample,hrates,hcapacity⟩:=
    hfinish p hp hpbound'
  let loadCap:=min loadLimit (min cap 1)
  have hload:0<loadCap:=by dsimp [loadCap];positivity
  have hloadLimit':loadCap≤loadLimit:=min_le_left _ _
  have hloadCap:loadCap≤cap:=(min_le_right _ _).trans (min_le_left _ _)
  have hloadOne:loadCap≤1:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨εsup,cap,δsample,loadCap,hp1,hpκ,hsqrt,hεsup,hεsupcap,hcap,hcapOther,hδsample,hload,hloadOne,?_,hrates,?_⟩
  · intro load ξ hload0 hloadSmall hξ hξSmall
    have hload1:load≤1:=hloadSmall.trans hloadOne
    have hh:=hcover lam load ξ hlam.le hlamcover hload0 (hloadSmall.trans hloadLimit') hload1 hξ hξSmall
    have hsq:load^2≤load:=by nlinarith [mul_nonneg hload0 (sub_nonneg.mpr hload1)]
    have hξcap:10*ξ≤cap:=by nlinarith [hξSmall,hsq,hloadSmall,hloadCap]
    refine ⟨?_,hξcap⟩
    simpa only [hellEq,target] using hh.1
  · intro ν hν hνcap
    obtain ⟨N,hN⟩:=hcapacity ν hν hνcap
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨horder,K,Dmax,hK,hD,hDcap,hbounds⟩:=hN n hn
    refine ⟨horder,K,Dmax,hK,hD,hDcap,?_⟩
    intro Lconf t η hL ht hη hηcap
    obtain ⟨hcomp,hcost⟩:=hbounds Lconf t η hL ht hη hηcap
    constructor
    · convert hcomp using 1 <;> congr 1 <;> ring
    · exact hcost
end Oberwolfach
