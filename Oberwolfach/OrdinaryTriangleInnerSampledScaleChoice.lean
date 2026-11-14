module

public import Oberwolfach.OrdinaryAsymmetricSampledCoverOrderedChoice

@[expose] public section
/-! Choose the vortex and root scales after the inner-domain tolerance, but
before the fresh sampling rate and cleanup errors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_inner_sampled_scale_choice
    (root edit eCoeff hCoeff εcap γ ζ:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff)
    (hεcap:0<εcap) (hγ:0<γ) (hζ:0<ζ):
    ∃lam ε βe βh θ:ℝ,0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ lam=2*ε^2 ∧ 0<lam ∧
      lam≤root ∧ lam≤1/4 ∧ βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      lam≤βe/4 ∧ lam≤βh/2 ∧ 3*lam≤edit/4 ∧ lam*3≤edit/4 ∧
      θ=ζ*(γ/4)*ε ∧ 0<θ ∧
    ∀pcap othercap:ℝ,0<pcap→0<othercap→
    ∃ellCap pbound:ℝ,ellCap=θ/64 ∧ 0<ellCap ∧ 0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→∃εsup cap δsample loadCap:ℝ,
      p≤1 ∧ p≤4*θ ∧ 20*Real.sqrt (2*p)≤θ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧ 0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧
      (∀load ξ:ℝ,0≤load→load≤loadCap→0≤ξ→ξ≤load^2/160→
        max (18*load+3*lam) ((3*load+lam)*3)≤ellCap ∧ 10*ξ≤cap) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θ*p/4 ∧ ν+η≤θ*p/4) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2≤θ*p*n/4:=by
  have hc:0<ζ*(γ/4):=by positivity
  obtain ⟨lam,ε,βe,βh,θ,hε,hεcap,hε1,hlamEq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,hlevel,hθeq,hθ,hrest⟩:=
      ordinary_asymmetric_sampled_cover_ordered_choice 2 root edit eCoeff hCoeff εcap (ζ*(γ/4))
        hroot hedit he hh hεcap hc
  refine ⟨lam,ε,βe,βh,θ,hε,hεcap,hε1,hlamEq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,?_,?_,hθ,?_⟩
  · norm_num at hlevel ⊢
    exact hlevel
  · exact hθeq
  intro pcap othercap hpcap hother
  obtain ⟨ellCap,k,pbound,hellEq,hell,hk,hpbound,hpboundCap,hfinish⟩:=
    hrest 1 pcap othercap (by norm_num) hpcap hother
  refine ⟨ellCap,pbound,hellEq,hell,hpbound,hpboundCap,?_⟩
  intro p hp hpbound'
  obtain ⟨εsup,cap,δsample,loadCap,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hδsample,
    hload,hload1,hcover,hrates,hcapacity⟩:=hfinish p hp hpbound'
  refine ⟨εsup,cap,δsample,loadCap,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hδsample,
    hload,hload1,?_,hrates,?_⟩
  · intro load ξ hload0 hloadSmall hξ hξSmall
    have hcvr:=hcover load ξ hload0 hloadSmall hξ hξSmall
    norm_num at hcvr ⊢
    exact hcvr
  · obtain ⟨N,hN⟩:=hcapacity 0 (by norm_num) hcap.le
    refine ⟨N,?_⟩
    intro n hn
    exact (hN n hn).1
end Oberwolfach
