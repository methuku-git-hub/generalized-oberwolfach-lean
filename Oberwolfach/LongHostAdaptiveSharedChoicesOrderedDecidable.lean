module

public import Oberwolfach.LongHostMatchingVortexAliasDecidable
public import Oberwolfach.LongHostAdaptiveMatchingSpacing

@[expose] public section
/-! Choose the host constants before the class count and later event scales. -/
set_option autoImplicit false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local irreducible] HostMatchingVortexContinuation SuppliedVortexEventContinuation

theorem long_host_adaptive_shared_choices_ordered_decidable
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
    HostMatchingVortexContinuation m K d αHost A BM BO ∧
    SuppliedVortexEventContinuation r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO := by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,hhost⟩:=
    long_host_matching_vortex_alias_decidable L₀ αHost hαHost
  subst m
  refine ⟨r+4,r,k₀,hm,hLm,heven,hr,rfl,hlen,hmarginHost,A,BM,hA,hBM,?_⟩
  intro ρ₀ hρ₀
  obtain ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγRich,hγRich1,hγcap,
    hmargin,hω,hpstar,hkstar,htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound⟩:=
    long_host_adaptive_reference_parameters (r+4) k₀ (le_trans (by decide : 1≤7) hm) αHost ρ₀ hαHost hρ₀ hmarginHost
  refine ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγRich,hγRich1,hγcap,
    hmargin,hω,hpstar,hkstar,htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound,?_⟩
  intro Qpow K hQpow hK θ ε₀ lam hθ hθmax hε₀ hlam hlamθ
  have hm' : 7≤r+4 := hm
  have hHostForD:∀d:ℕ,2≤d→∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation (r+4) K d αHost A BM BO:=by
    intro d hd
    obtain ⟨BO,hBO,hhost'⟩:=hhost K d (lt_of_lt_of_le (by decide : 0<3) hK) hd
    exact ⟨BO,hBO,hhost'⟩
  obtain ⟨eps,heps,heps1,hepsAssign,d,hd,hcut,halpha,halphaMass,hγ,hγε,BO,hBO,hHost',hEvent⟩:=
    long_host_adaptive_matching_spacing r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK hm' θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ αHost A BM hBM hHostForD
  have hHost:HostMatchingVortexContinuation (r+4) K d αHost A BM BO:=hHost'
  exact ⟨eps,heps,heps1,hepsAssign,d,hd,hcut,halpha,halphaMass,hγ,hγε,BO,hBO,hHost,hEvent⟩
end Oberwolfach
