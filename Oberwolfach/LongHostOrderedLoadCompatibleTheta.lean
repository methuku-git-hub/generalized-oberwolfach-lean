module

public import Oberwolfach.LongHostOrderedWithPrescribedHubMargins
public import Oberwolfach.FirstVortexThetaChoice

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local irreducible] HostMatchingVortexContinuation SuppliedVortexFixedSpacingEventWithInnerColumn HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatchingAndOrderedLocalRetentionRates

theorem long_host_ordered_with_load_compatible_theta
    (L₀:ℕ) (αHost ρ₀:ℝ) (hαHost:0<αHost) (hρ₀:0<ρ₀):
    ∃b α:ℝ,0<b ∧ 0<α ∧ α/16≤b ∧ (∀ρ:ℝ,ρ₀/4≤ρ→b≤(ρ/40000)/16) ∧
    ∃m r k₀:ℕ,∃hm:7≤m,∃hLm:L₀≤m,4/(m:ℝ)≤b/2 ∧ ∃heven:Even (m+1),∃hr:2≤r,
    ∃hrm:r+4=m,∃hlen:r+4+1=(k₀+2)*2,
    ∃hmarginHost:successorCycleRatio k₀+αHost/4≤1/2+αHost/2,
    ∃A BM:ℝ,∃hA:0<A,∃hBM:0<BM,
    ∃αRef γRich ω pstarRef kstar tstar:ℝ,
    αRef=αHost/2 ∧
    ∃hαRef:0<αRef,∃hγRich:0<γRich,∃hγRich1:γRich≤1/2,∃hγcap:γRich≤αRef,
    ∃hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef,
    ∃hω:0<ω,∃hpstar:0<pstarRef,∃hkstar:0<kstar,
    ∃htstar:0<tstar,∃htstar100:tstar≤1/100,∃htstar1:tstar≤1,
    ∃hωBound:4*ω≤ρ₀,∃hpstarBound:4*(m:ℝ)*pstarRef≤ρ₀*(1/100),
    ∃htm:tstar≤(1/100)/(m:ℝ),
    (∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2) ∧
    ∀(Qpow:ℕ) (hQpow:0<Qpow) (δ θMax:ℝ) (hδ:0<δ) (hθMax:0<θMax),
    ∃θ:ℝ,∃hθ:0<θ,∃hθmax:θ≤1/100,θ≤θMax ∧ θ≤δ/32 ∧ 10*θ≤δ ∧
    ∀(ζretMax:ℝ) (hζretMax:0<ζretMax),
    ∃βList:ℝ,0<βList ∧ βList≤1 ∧
    ∃d K:ℕ,∃hd:2≤d,∃hdlarge:(r+4)+2≤d,∃hK:3≤K,∃hK5:5≤K,∃hinv:1/(d:ℝ)≤θ/1024,
    ∃hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ,
    5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    1/(8*(d:ℝ))≤θ/2 ∧ 1/(4*(d:ℝ))≤(5/64:ℝ)*θ^2 ∧
    (∃N:ℕ,∀n:ℕ,N≤n→5*(n:ℝ)^(3/4:ℝ)≤(5*θ^2*ρ₀/1024)*n) ∧
    (∀(ε δ lamMax ζMax:ℝ),0<ε→0<δ→0<lamMax→0<ζMax→
      ∃lam ζList:ℝ,0<lam ∧ lam≤θ ∧ lam≤lamMax ∧ lam≤δ*ε/32 ∧ 0<ζList ∧ ζList≤ζMax ∧ ζList≤lam/3 ∧
      ∃NList:ℕ,∀n≥NList,
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
        βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*θ ∧
        (lam+2*ζList)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤βList*n) ∧
    ∃ζret:ℝ,∃hζret:0<ζret,ζret≤ζretMax ∧ ∃Nret:ℕ,
    (∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n) ∧
    ∃BO:Fin K→ℝ,∃hBO:∀i,0<BO i,
    ∃hαmargin:2*αRef≤αHost,
    ∃htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ),
    ∃hkBound':∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2,
    HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatchingAndOrderedLocalRetentionRates r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ζret hζret d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound' :=by
  obtain ⟨b,α,hb,hα,hαb,hρ,m,r,k₀,hm,hLm,hpath,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,
    αRef,γRich,ω,pstarRef,kstar,tstar,hEq,hαRef,hγRich,hγRich1,hγcap,hmargin,hω,hpstar,hkstar,
    htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound,hLate⟩:=
    long_host_first_inner_column_ordered_with_prescribed_hub_margins L₀ αHost ρ₀ hαHost hρ₀
  refine ⟨b,α,hb,hα,hαb,hρ,m,r,k₀,hm,hLm,hpath,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,
    αRef,γRich,ω,pstarRef,kstar,tstar,hEq,hαRef,hγRich,hγRich1,hγcap,hmargin,hω,hpstar,hkstar,
    htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound,?_⟩
  intro Qpow hQpow δ θMax hδ hθMax
  obtain ⟨θ,hθ,hθmax,hθcap,hθlocal,hθδ⟩:=first_vortex_theta_choice δ θMax hδ hθMax
  refine ⟨θ,hθ,hθmax,hθcap,hθlocal,hθδ,?_⟩
  intro ζretMax hζretMax
  exact hLate Qpow hQpow θ hθ hθmax ζretMax hζretMax
end Oberwolfach
