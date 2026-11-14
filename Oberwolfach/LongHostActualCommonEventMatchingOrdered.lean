module

public import Oberwolfach.LongHostActualEventMatching
public import Oberwolfach.LongHostActualEventConclusion
public import Oberwolfach.LongHostAdaptiveSharedChoicesOrderedDecidable

@[expose] public section
/-! Compose the checked host-event specialization while choosing host constants
before the class count and later event parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local irreducible] HostMatchingVortexContinuation SuppliedVortexEventContinuation HostVortexActualEventConclusionWithMatching

theorem long_host_actual_common_event_with_matching_ordered
    (L₀:ℕ) (αHost:ℝ) (hαHost:0<αHost) :
    ∃ m r k₀:ℕ,
    ∃ hm:7≤m, ∃ hLm:L₀≤m, ∃ heven:Even (m+1), ∃ hr:2≤r,
    ∃ hrm:r+4=m, ∃ hlen:r+4+1=(k₀+2)*2,
    ∃ hmarginHost:successorCycleRatio k₀+αHost/4≤1/2+αHost/2,
    ∃ A BM:ℝ, ∃ hA:0<A, ∃ hBM:0<BM,
    ∀ (ρ₀:ℝ) (hρ₀:0<ρ₀),
    ∃ αRef γRich ω pstarRef kstar tstar:ℝ,
    αRef=αHost/2 ∧
    ∃ hαRef:0<αRef, ∃ hγRich:0<γRich, ∃ hγRich1:γRich≤1/2,
    ∃ hγcap:γRich≤αRef,
    ∃ hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef,
    ∃ hω:0<ω, ∃ hpstar:0<pstarRef, ∃ hkstar:0<kstar,
    ∃ htstar:0<tstar, ∃ htstar100:tstar≤1/100, ∃ htstar1:tstar≤1,
    ∃ hωBound:4*ω≤ρ₀, ∃ hpstarBound:4*(m:ℝ)*pstarRef≤ρ₀*(1/100),
    ∃ htm:tstar≤(1/100)/(m:ℝ),
    (∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2) ∧
    ∀ (Qpow K:ℕ) (hQpow:0<Qpow) (hK:3≤K)
      (θ ε₀ lam:ℝ) (hθ:0<θ) (hθmax:θ≤1/100) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ),
    ∃ eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    ∃ d:ℕ, ∃ hd:2≤d, ∃ hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ,
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∃ BO:Fin K→ℝ, ∃ hBO:∀i,0<BO i,
    ∃ hαmargin:2*αRef≤αHost,
    ∃ htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ),
    ∃ hkBound':∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2,
    HostVortexActualEventConclusionWithMatching r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound' := by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,hLate⟩:=
    long_host_adaptive_shared_choices_ordered_decidable L₀ αHost hαHost
  refine ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,?_⟩
  intro ρ₀ hρ₀
  obtain ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγRich,hγRich1,hγcap,
    hmargin,hω,hpstar,hkstar,htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound,hLate⟩:=hLate ρ₀ hρ₀
  refine ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγRich,hγRich1,hγcap,
    hmargin,hω,hpstar,hkstar,htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound,?_⟩
  intro Qpow K hQpow hK θ ε₀ lam hθ hθmax hε₀ hlam hlamθ
  obtain ⟨eps,heps,heps1,hepsAssign,d,hd,hcut,halpha,halphaMass,hγ,hγε,BO,hBO,hHost,hEvent⟩:=
    hLate Qpow K hQpow hK θ ε₀ lam hθ hθmax hε₀ hlam hlamθ
  have hαmargin:2*αRef≤αHost:=by linarith
  have htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ):=by simpa only [hrm] using htm
  have hkBound':∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2:=by
    simpa only [hrm] using hkBound
  refine ⟨eps,heps,heps1,hepsAssign,d,hd,hcut,halpha,halphaMass,hγ,hγε,BO,hBO,
    hαmargin,htstarBound,hkBound',?_⟩
  apply host_vortex_actual_event_with_matching r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound'
  unfold HostVortexActualEventConclusion
  apply long_host_supplied_event_specialization r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound'
  · simpa only [hrm] using hHost
  · exact hEvent
end Oberwolfach
