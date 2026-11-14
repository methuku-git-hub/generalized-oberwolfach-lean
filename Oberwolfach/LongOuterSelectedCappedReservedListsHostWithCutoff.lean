module

public import Oberwolfach.LongHostMatchingSelectedCappedReservedLists
public import Oberwolfach.LongOuterMatchingSourceParametersWithCutoff

@[expose] public section
/-! Fix the common matching/source spacing and cutoff before the host order,
retaining the matching-selected event, losses, error and actual weights. -/
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
theorem long_host_matching_outer_selected_capped_reserved_lists_choices_with_cutoff
    (L₀ dMin KMin:ℕ) (αHost ρ₀ εcap:ℝ) (hεcap:0<εcap) (hα:0<αHost) (hα1:αHost≤1)
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
    ∀(θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100),
    ∃d K Nsource:ℕ,∃hd3:3≤d,∃hdMin:dMin≤d,∃hd:2≤d,∃hK:3≤K,∃hKMin:KMin≤K,
    ∃hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ,
      1/(8*(d:ℝ))≤θ/2 ∧
      5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K+1)≤θ/2 ∧
      (∀n≥Nsource,8*((((r+4):ℕ):ℝ)+1)/θ<(n:ℝ)^((1:ℝ)/4)) ∧
    ∀(Qpow:ℕ) (hQpow:0<Qpow) (ε₀ lam:ℝ) (hε₀:ε₀<1)
      (hlam:0<lam) (hlamθ:lam≤θ),
    ∃BO:Fin K→ℝ,∃hBO:(∀i,0<BO i), LongHostMatchingGeometryContinuation m K d αHost A BM BO ∧
      LongNamedMatchingSelectedCappedReservedListsForWeights r (r+12) k₀ Qpow hr hQpow hlen
        αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
        hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar K hK
        (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
        (by simpa only [hrm] using htcap) d hd hcut
        (αHost/16) (ρ₀/400) (αHost/2) (ρ₀/8) tstar kstar
        (successorWeightLower k₀ (αHost/4)) (successorWeightUpper k₀ (αHost/4)) BM hBM BO hBO εcap := by
  obtain ⟨c₀,m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,
    αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγ,hγ1,hγcap,hmargin,hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound,hhost⟩:=
    long_host_matching_selected_capped_reserved_lists_weight_choices L₀ αHost ρ₀ εcap hεcap hα hα1 hρ₀ hρ₀1
  refine ⟨c₀,m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,
    αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγ,hγ1,hγcap,hmargin,hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound,?_⟩
  intro θ hθ hθmax
  obtain ⟨d,K,Nsource,hd3,hdMin,hK,hKMin,hcut,hspace,hsource,hN⟩:=
    long_outer_matching_source_parameters_with_cutoff (r+4) dMin KMin θ hθ
  have hd:2≤d:=by omega
  refine ⟨d,K,Nsource,hd3,hdMin,hd,hK,hKMin,hcut,hspace,hsource,hN,?_⟩
  intro Qpow hQpow ε₀ lam hε₀ hlam hlamθ
  exact hhost Qpow K d hQpow hK hd θ ε₀ lam hθ hθmax hε₀ hlam hlamθ hcut
end Oberwolfach
