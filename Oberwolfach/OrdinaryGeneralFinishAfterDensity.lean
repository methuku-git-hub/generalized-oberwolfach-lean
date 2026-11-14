module

public import Oberwolfach.OrdinaryBoundaryCompletionTraceUniform
public import Oberwolfach.OrdinaryRootFirstRatesAfterDensity

@[expose] public section
/-! Choose a general-wheel completion capacity and a density cap first;
    after the actual density is chosen, allow independently smaller root,
    packing and cleanup errors and a common completion capacity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_finish_after_density (m:ℕ) (βe κ ζ rate pcap othercap:ℝ)
    (hβe:0<βe) (hκ:0<κ) (hζ:0<ζ) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap):
    ∃k pbound:ℝ,0<k ∧ 0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→
    ∃εsup cap:ℝ,p≤1 ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤cap→
        τ+ν≤p^2/4 ∧ τ+ν+ell≤ζ*κ*p/4 ∧ ν+η≤ζ*κ*p/4) ∧
    ∀ν:ℝ,0≤ν→ν≤cap→∃N:ℕ,∀n:ℕ,N≤n→
      2≤ζ*κ*p*n/4 ∧
      ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧
      (Dmax:ℝ)≤k^2*n ∧
      ∀(Lconf t η:ℝ),Lconf≤k^2*n→t≤ν*n→0≤η→η≤cap→
        ((n*Dmax*(m+1):ℕ):ℝ)/(K:ℝ)+
          (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
          (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/2)*n-3*t ∧
        ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*n :=by
  obtain ⟨k,hk,hk1,hcapacity⟩:=ordinary_boundary_completion_trace_budget_uniform_capacity m (βe/2) (rate/2)
    (by positivity) (by positivity)
  let pcap':=min pcap (k^2/4)
  let cap':=min othercap (min (k^2/2) (rate/2))
  have hpcap':0<pcap':=by dsimp [pcap'];positivity
  have hcap':0<cap':=by dsimp [cap'];positivity
  obtain ⟨pbound,hpbound,hpcapbound,hrates⟩:=
    ordinary_root_first_rates_after_density κ ζ (rate/2) pcap' cap' hκ hζ (by positivity) hpcap' hcap'
  refine ⟨k,pbound,hk,hpbound,hpcapbound.trans (min_le_left _ _),?_⟩
  intro p hp hpbound'
  have hpK:p≤k^2/4:=hpbound'.trans (hpcapbound.trans (min_le_right _ _))
  obtain ⟨εsup,cap,hp1,hpκ,hsqrt,hεsup,hεcap,hcap,hcapbound,hrates,Norder,horder⟩:=hrates p hp hpbound'
  have hcapOther:cap≤othercap:=hcapbound.trans (min_le_left _ _)
  have hcapK:cap≤k^2/2:=hcapbound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcapRate:cap≤rate/2:=hcapbound.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρK:2*p≤k^2:=by nlinarith [sq_nonneg k]
  refine ⟨εsup,cap,hp1,hpκ,hsqrt,hεsup,hεcap,hcap,hcapOther,?_,?_⟩
  · intro τ ν η ell hτ hν hη hell hτcap hνcap hηcap hellcap
    obtain ⟨ha,hb,hc,_⟩:=hrates τ ν η ell hτ hν hη hell hτcap hνcap hηcap hellcap
    exact ⟨ha,hb,hc⟩
  · intro ν hν hνcap
    have hνK:ν≤k^2:=by nlinarith [sq_nonneg k]
    obtain ⟨Ncap,hNcap⟩:=hcapacity (k^2) (k^2) (2*p) ν (by positivity) (by positivity) (by positivity) hν
      le_rfl le_rfl hρK hνK
    let N:=max (max Ncap Norder) ⌈2/k^2⌉₊
    refine ⟨N,?_⟩
    intro n hn
    have hnCap:Ncap≤n:=by dsimp [N] at hn;omega
    have hnOrder:Norder≤n:=by dsimp [N] at hn;omega
    have hnCeil:⌈2/k^2⌉₊≤n:=by dsimp [N] at hn;omega
    have hk2:0<k^2:=sq_pos_of_pos hk
    have hnReal:(2/k^2:ℝ)≤n:=(Nat.le_ceil _).trans (by exact_mod_cast hnCeil)
    have hsize:2≤k^2*n:=by
      have hh:2≤(n:ℝ)*k^2:=(div_le_iff₀ hk2).mp hnReal
      nlinarith only [hh]
    let Dmax:=⌈(2*p)*(n:ℝ)⌉₊
    have hDlow:(2*p)*n≤(Dmax:ℝ):=Nat.le_ceil _
    have hDhigh:(Dmax:ℝ)≤(2*p)*n+1:=(Nat.ceil_lt_add_one (by positivity:0≤(2*p)*(n:ℝ))).le
    have hDcap:(Dmax:ℝ)≤k^2*n:=by
      have hh:=mul_le_mul_of_nonneg_right hpK (Nat.cast_nonneg n)
      nlinarith only [hh,hDhigh,hsize]
    obtain ⟨K,hK,_,hKall⟩:=hNcap n hnCap
    refine ⟨horder n hnOrder,K,Dmax,hK,hDlow,hDcap,?_⟩
    intro Lconf t η hL ht hη hηcap
    obtain ⟨hext,hload⟩:=hKall Dmax Lconf t hDcap hL ht
    refine ⟨hext,?_⟩
    have hηbound:η*n≤(rate/2)*n:=mul_le_mul_of_nonneg_right (hηcap.trans hcapRate) (Nat.cast_nonneg n)
    nlinarith only [hload,hηbound]
end Oberwolfach
