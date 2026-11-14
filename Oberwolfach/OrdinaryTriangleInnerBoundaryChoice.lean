module

public import Oberwolfach.OrdinaryAsymmetricSampledCoverOrderedChoice

@[expose] public section
/-! Choose a matching margin small enough both for the inner triangle
factor and for the two cleanup boundary allowances, before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_inner_boundary_choice
    (root edit eCoeff hCoeff εcap γ ζ:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff)
    (hεcap:0<εcap) (hγ:0<γ) (hζ:0<ζ):
    ∃lam ε βe βh θ:ℝ,0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ lam=2*ε^2 ∧ 0<lam ∧
      lam≤root ∧ lam≤1/4 ∧ βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      lam≤βe/4 ∧ lam≤βh/2 ∧ 3*lam≤edit/4 ∧ lam*3≤edit/4 ∧
      0<θ ∧ θ≤ζ*(γ/4)*ε ∧ θ≤βe ∧ θ≤βh ∧
    ∀pcap othercap:ℝ,0<pcap→0<othercap→
    ∃ellCap pbound:ℝ,ellCap=θ/64 ∧ 0<ellCap ∧ ellCap≤βe/8 ∧ ellCap≤βh/4 ∧
      0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→∃εsup cap δsample loadCap:ℝ,
      p≤1 ∧ p≤4*θ ∧ 20*Real.sqrt (2*p)≤θ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧ cap≤βe/8 ∧ cap≤βh/4 ∧
      0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧
      βe+3*max cap ellCap≤2*βe ∧ βh+2*ellCap≤2*βh ∧
      (∀load ξ:ℝ,0≤load→load≤loadCap→0≤ξ→ξ≤load^2/160→
        max (18*load+3*lam) ((3*load+lam)*3)≤ellCap ∧ 10*ξ≤cap) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θ*p/4 ∧ ν+η≤θ*p/4) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2≤θ*p*n/4:=by
  let c:ℝ:=min (ζ*(γ/4)) (min eCoeff hCoeff)/2
  have hc:0<c:=by dsimp [c];positivity
  have hc1:c≤ζ*(γ/4):=by
    have hh:=min_le_left (ζ*(γ/4)) (min eCoeff hCoeff)
    have hz:0≤ζ*(γ/4):=by positivity
    dsimp [c];linarith
  have hcE:c≤eCoeff:=by
    have hh:(min (ζ*(γ/4)) (min eCoeff hCoeff))≤eCoeff:=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp [c];linarith
  have hcH:c≤hCoeff:=by
    have hh:(min (ζ*(γ/4)) (min eCoeff hCoeff))≤hCoeff:=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp [c];linarith
  obtain ⟨lam,ε,βe,βh,θ,hε,hεcap,hε1,hlamEq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,hlevel,hθeq,hθ,hrest⟩:=
      ordinary_asymmetric_sampled_cover_ordered_choice 2 root edit eCoeff hCoeff εcap c hroot hedit he hh hεcap hc
  have hθ1:θ≤ζ*(γ/4)*ε:=by
    rw [hθeq]
    exact mul_le_mul_of_nonneg_right hc1 hε.le
  have hθE:θ≤βe:=by rw [hθeq,hβeeq];exact mul_le_mul_of_nonneg_right hcE hε.le
  have hθH:θ≤βh:=by rw [hθeq,hβheq];exact mul_le_mul_of_nonneg_right hcH hε.le
  refine ⟨lam,ε,βe,βh,θ,hε,hεcap,hε1,hlamEq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,?_,hθ,hθ1,hθE,hθH,?_⟩
  · norm_num at hlevel ⊢
    exact hlevel
  intro pcap othercap hpcap hother
  let other:=min othercap (min (βe/8) (βh/4))
  have hother':0<other:=by dsimp [other];positivity
  obtain ⟨ellCap,k,pbound,hellEq,hell,hk,hpbound,hpboundCap,hfinish⟩:=
    hrest 1 pcap other (by norm_num) hpcap hother'
  have hellE:ellCap≤βe/8:=by rw [hellEq];linarith only [hθE,hβe]
  have hellH:ellCap≤βh/4:=by rw [hellEq];linarith only [hθH,hβh]
  refine ⟨ellCap,pbound,hellEq,hell,hellE,hellH,hpbound,hpboundCap,?_⟩
  intro p hp hpbound'
  obtain ⟨εsup,cap,δsample,loadCap,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hδsample,
    hload,hload1,hcover,hrates,hcapacity⟩:=hfinish p hp hpbound'
  have hcapO:cap≤othercap:=hcapOther.trans (min_le_left _ _)
  have hcapE:cap≤βe/8:=hcapOther.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcapH:cap≤βh/4:=hcapOther.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmax:max cap ellCap≤βe/8:=max_le hcapE hellE
  have hprofileE:βe+3*max cap ellCap≤2*βe:=by linarith
  have hprofileH:βh+2*ellCap≤2*βh:=by linarith
  refine ⟨εsup,cap,δsample,loadCap,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcap,hcapO,hcapE,hcapH,hδsample,
    hload,hload1,hprofileE,hprofileH,?_,hrates,?_⟩
  · intro load ξ hload0 hloadSmall hξ hξSmall
    have hcvr:=hcover load ξ hload0 hloadSmall hξ hξSmall
    norm_num at hcvr ⊢
    exact hcvr
  · obtain ⟨N,hN⟩:=hcapacity 0 (by norm_num) hcap.le
    refine ⟨N,?_⟩
    intro n hn
    exact (hN n hn).1
end Oberwolfach
