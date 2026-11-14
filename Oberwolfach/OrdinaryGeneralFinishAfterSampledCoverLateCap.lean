module

public import Oberwolfach.OrdinaryGeneralFinishAfterDensityLateCap

@[expose] public section
/-! The total root-cover rate can be fixed before the sampling density:
only its sampled share enters the boundary matching margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_finish_after_sampled_cover_late_cap (m:ℕ) (βe κ ζ rate pcap:ℝ)
    (hβe:0<βe) (hκ:0<κ) (hζ:0<ζ) (hrate:0<rate) (hpcap:0<pcap):
    ∃ellCap k pbound:ℝ,ellCap=ζ*κ/64 ∧ 0<ellCap ∧ 0<k ∧ 0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→∀othercap:ℝ,0<othercap→
    ∃εsup cap δsample:ℝ,p≤1 ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧ 0<δsample ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤ζ*κ*p/4 ∧ ν+η≤ζ*κ*p/4) ∧
    ∀ν:ℝ,0≤ν→ν≤cap→∃N:ℕ,∀n:ℕ,N≤n→
      2≤ζ*κ*p*n/4 ∧
      ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤k^2*n ∧
      ∀(Lconf t η:ℝ),Lconf≤k^2*n→t≤ν*n→0≤η→η≤cap→
        ((n*Dmax*(m+1):ℕ):ℝ)/(K:ℝ)+
          (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
          (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/2)*n-3*t ∧
        ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n :=by
  obtain ⟨k,pbound,hk,hpbound,hpcapbound,hfinish⟩:=
    ordinary_general_finish_after_density_late_cap m βe κ (ζ/2) rate pcap hβe hκ (by positivity) hrate hpcap
  let ellCap:=ζ*κ/64
  have hell:0<ellCap:=by dsimp [ellCap];positivity
  refine ⟨ellCap,k,pbound,rfl,hell,hk,hpbound,hpcapbound,?_⟩
  intro p hp hpbound' othercap hother
  obtain ⟨εsup,cap,hp1,hpκ,hsqrt,hε,hεcap,hcap,hcapOther,hrates,hcapacity⟩:=hfinish p hp hpbound' othercap hother
  let δsample:=ζ*κ*p/64
  have hδ:0<δsample:=by dsimp [δsample];positivity
  have hzk:0≤ζ*κ:=by positivity
  have hmul:0≤ζ*κ*p:=by positivity
  refine ⟨εsup,cap,δsample,hp1,by nlinarith only [hpκ,hzk],by nlinarith only [hsqrt,hzk],
    hε,hεcap,hcap,hcapOther,hδ,?_,?_⟩
  · intro τ ν η ell hτ hν hη hell0 hτcap hνcap hηcap hellcap
    obtain ⟨ha,hb,hc⟩:=hrates τ ν η 0 hτ hν hη (by norm_num) hτcap hνcap hηcap hcap.le
    have hellp:=mul_le_mul_of_nonneg_left hellcap hp.le
    dsimp [ellCap] at hellp
    dsimp [δsample]
    refine ⟨ha,?_,?_⟩ <;> nlinarith only [hb,hc,hellp,hmul]
  · intro ν hν hνcap
    obtain ⟨N,hN⟩:=hcapacity ν hν hνcap
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨horder,K,Dmax,hK,hD,hDcap,hbound⟩:=hN n hn
    have hmuln:0≤ζ*κ*p*(n:ℝ):=by positivity
    refine ⟨by nlinarith only [horder,hmuln],K,Dmax,hK,hD,hDcap,hbound⟩
end Oberwolfach
