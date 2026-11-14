module

public import Oberwolfach.LongNamedHighProbParentListsWeights
public import Oberwolfach.LongNamedMatchingUniformParentWeights
public import Oberwolfach.LongNamedMatchingUniformParentLevel
public import Oberwolfach.LongActualReferenceLevelDensities

@[expose] public section
/-! Use the configuration constants returned by the named matching event
in the uniform-level continuation, keeping the host weights and parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem long_host_high_prob_matching_configured_lists_weight_choices
    (L₀:ℕ) (αHost ρ₀:ℝ) (hα:0<αHost) (hα1:αHost≤1)
    (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1):
    ∃c₀ m r k₀:ℕ,∃hm:7≤m,∃hLm:max L₀ c₀≤m,∃heven:Even (m+1),∃hr:2≤r,∃hrm:r+4=m,
    ∃hlen:r+4+1=(k₀+2)*2,
    ∃hmarginHost:successorCycleRatio k₀+αHost/4≤1/2+αHost/2,
    ∃A BM:ℝ,∃hA:0<A,∃hBM:0<BM,
    ∃αRef γRich ω pstarRef kstar tstar:ℝ,
    αRef=αHost/2 ∧
    ∃hαRef:0<αRef,∃hγRich:0<γRich,∃hγRich1:γRich≤1/2,∃hγcap:γRich≤αRef,
    ∃hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef,
    ∃hω:0<ω,∃hpstar:0<pstarRef,∃hkstar:0<kstar,
    ∃htstar:0<tstar,∃htstar100:tstar≤1/100,∃htstar1:tstar≤1,
    ∃hωBound:4*ω≤ρ₀,∃hpstarBound:4*(m:ℝ)*pstarRef≤ρ₀*(1/100),
    ∃htExact:tstar=(1/100)/(m:ℝ),∃htcap:tstar≤(1/100)/(m:ℝ),
    (∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2) ∧
    ∀(Qpow K d:ℕ) (hQpow:0<Qpow) (hK:3≤K) (hd:2≤d)
      (θ ε₀ lam ηEvent:ℝ) (hθ:0<θ) (hθmax:θ≤1/100) (hηEvent:0<ηEvent) (hε₀:ε₀<1)
      (hlam:0<lam) (hlamθ:lam≤θ)
      (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ),
    ∃BO:Fin K→ℝ,∃hBO:(∀i,0<BO i), LongHostMatchingGeometryContinuation m K d αHost A BM BO ∧
      LongNamedMatchingHighProbParentListsForWeights r (r+12) k₀ Qpow hr hQpow hlen
        αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
        hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar K hK
        (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam ηEvent hηEvent hε₀ hlam hlamθ
        (by simpa only [hrm] using htcap) d hd hcut
        (αHost/16) (ρ₀/400) (αHost/2) (ρ₀/8) tstar kstar
        (successorWeightLower k₀ (αHost/4)) (successorWeightUpper k₀ (αHost/4)) BM hBM BO hBO := by
  obtain ⟨c₀,hLevel,hhost⟩:=long_host_named_matching_and_uniform_level_choices L₀ αHost ρ₀ hα hα1 hρ₀ hρ₀1
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,hhost⟩:=hhost
  obtain ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγ,hγ1,hγcap,hmargin,hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound,hhost⟩:=hhost ρ₀ hρ₀
  have hm1:1≤m:=by omega
  have hrc:c₀≤r+5:=by omega
  have hden:=long_actual_reference_level_densities m hm1 ρ₀ ρ₀ tstar kstar hρ₀ le_rfl hρ₀1 ht htcap hk (hkbound ρ₀ le_rfl).2
  obtain ⟨_,hω0,_,_,_,_,_,_,hkhalf,_⟩:=hden
  obtain ⟨hLower,hUpper⟩:=successorWeightConstants_pos k₀ (αHost/4) (by positivity)
  refine ⟨c₀,m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,
    αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγ,hγ1,hγcap,hmargin,hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound,?_⟩
  intro Qpow K d hQpow hK hd θ ε₀ lam ηEvent hθ hθmax hηEvent hε₀ hlam hlamθ hcut
  obtain ⟨BO,hBO,hhost,_⟩:=hhost Qpow K d hQpow hK hd θ ε₀ lam hθ hθmax hε₀ hlam hlamθ hcut
  refine ⟨BO,hBO,hhost,?_⟩
  exact long_named_matching_high_prob_parent_lists_for_host_weights r (r+12) k₀ Qpow hr hQpow hlen
    αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
    hmargin hγ hγ1 hγcap ht ht1 ht100 hk K hK (by simpa only [hrm] using hm)
    θ ρ₀ hθ hθmax hρ₀ hωb ε₀ lam ηEvent hηEvent hε₀ hlam hlamθ (by simpa only [hrm] using htcap) d hd hcut
    c₀ (αHost/16) (ρ₀/400) (αHost/2) (ρ₀/8) tstar kstar
    (successorWeightLower k₀ (αHost/4)) (successorWeightUpper k₀ (αHost/4))
    hLevel hrc hρ₀1 hω0 ht ht1 hk hkhalf hLower hUpper BM hBM BO hBO
end Oberwolfach
