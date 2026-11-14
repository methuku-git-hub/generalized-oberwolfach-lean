module

public import Oberwolfach.OrdinaryRootFirstTraceRates

@[expose] public section
/-! The four later error rates may each be chosen independently below a
    common earlier cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_trace_rates_monotone (κ ζ rate pcap othercap:ℝ)
    (hκ:0<κ) (hζ:0<ζ) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap):
    ∃p εsup cap:ℝ,
      0<p ∧ p≤1 ∧ p≤pcap ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤cap→
        τ+ν≤p^2/4 ∧ τ+ν+ell≤ζ*κ*p/4 ∧ ν+η≤ζ*κ*p/4 ∧ ν+η+4*p≤rate) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2≤ζ*κ*p*n/4 :=by
  obtain ⟨p,εsup,τ,ν,η,ell,hp,hp1,hpcap,hpκ,hsqrt,hε,hεcap,hτ,hν,hη,hell,
    hτcap,hνcap,hηcap,hellcap,hsupport,hclass,hblock,hcost,N,hN⟩:=
    ordinary_root_first_trace_rates κ ζ rate pcap othercap hκ hζ hrate hpcap hother
  let cap:=min τ (min ν (min η ell))
  have hc:0<cap:=by dsimp [cap];exact lt_min hτ (lt_min hν (lt_min hη hell))
  have hcτ:cap≤τ:=min_le_left _ _
  have hcν:cap≤ν:=(min_le_right _ _).trans (min_le_left _ _)
  have hcη:cap≤η:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcell:cap≤ell:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨p,εsup,cap,hp,hp1,hpcap,hpκ,hsqrt,hε,hεcap,hc,hcτ.trans hτcap,?_,N,hN⟩
  intro τ' ν' η' ell' _ _ _ _ hτ' hν' hη' hell'
  have ht:=hτ'.trans hcτ
  have hv:=hν'.trans hcν
  have he:=hη'.trans hcη
  have hl:=hell'.trans hcell
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith
end Oberwolfach
