module

public import Oberwolfach.OrdinaryAbundanceReservationPlacementRates
public import Oberwolfach.CandidateOrdinarySelectedOriginalMatchingOccupancy
public import Oberwolfach.OrdinaryAbundanceMatchingReservation

@[expose] public section
/-! Select the seed before the matching geometry; the original abundance then
supplies the reserved components and the candidate class on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryCandidateAbundancePlacementOccupancyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_abundance_selected_matching_occupancy_and_placement_rates
    (L rstar:ℕ) (β θ α δ:ℝ) (hr:3≤rstar) (hβ:0<β) (hβ1:β≤1) (hθ:0<θ) (hθ1:θ≤1/100) (hα:0<α)
    (hδ:0<δ) (hθδ:θ≤δ/8):
    ∃m k d K rank:ℕ,L≤m ∧ 7≤m ∧ Even (m+1) ∧ m+1=(k+2)*2 ∧
      successorCycleRatio k+α/2≤1/2+α ∧
      2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤β ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    (∀αCap:ℝ,0<αCap→∃κ b z ζret matchErr:ℝ,0<κ ∧ 0<b ∧ 0<z ∧ 0<ζret ∧ 0<matchErr ∧
      b≤αCap/16 ∧ b≤δ/8 ∧
      16/(d:ℝ)+16*κ+16*b/αCap+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+matchErr≤(δ/8)/2) ∧
    ∃smin:ℝ,0<smin ∧
    ∀(hd' : 2≤d) (ρ₀ t ξ ζ θhost τ:ℝ),
      1/2≤θhost→0<ρ₀→0<t→0<ξ→0<ζ→0<τ→
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2),
    (∀u,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))→
    ∀(D:ℕ),0<D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    ∀(Allowed:Set ℕ), (∀u,AllowedCycleLengths (F u) Allowed)→
      (∀r∈Allowed,cycleThreshold r≤θhost)→
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→
    ∀(π:Equiv.Perm (Fin n)),(θhost+α)*(n:ℝ)≤D→
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∃(i₀:Fin K) (rsv:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=rstar ∧ smin≤rsv ∧ rsv≤1/100 ∧ rsv≤1/(2*(K:ℝ)) ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=rstar) ∧
      (∀u,(rstar:ℝ)*(C u).card=rsv*n) ∧
      (∀u,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n) ∧
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d,
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd' q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D (ordinaryEligibleHost P π d) π d w;
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+3*ζ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/((m:ℝ)+1)+4*(n:ℝ)^(3/4:ℝ)) ∧
      ∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨m,k,hL,hm,heven,hlen,hratio,hcore⟩:=ordinary_selected_original_weighted_matching_occupancy_candidate L α hα
  obtain ⟨d,K,rank,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hrates,smin,hsmin,Nres,hres⟩:=
    ordinary_abundance_reservation_with_placement_rates β θ δ hβ hβ1 hθ hθ1 hδ hθδ rstar m hr
  refine ⟨m,k,d,K,rank,hL,hm,heven,hlen,hratio,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hrates,smin,hsmin,?_⟩
  intro hd' ρ₀ t ξ ζ θhost τ hθhost hρ₀ ht hξ hζ hτ
  obtain ⟨Ncore,hcore⟩:=hcore K d hd ρ₀ t ξ ζ smin θhost θ τ hθhost hρ₀ ht hξ hζ hsmin hθ hτ
  refine ⟨max Nres Ncore,?_⟩
  intro n hn hn0 U _ _ hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  obtain ⟨i₀,rsv,C,hi,hslo,hs1,hsclass,hclass,hsize,hcard,hreserve⟩:=hres n (by omega) U F hF hfreq
  have hc:(8:ℝ)≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  obtain ⟨sampling,w,seed,hmatch⟩:=hcore n (by omega) hn0 U hUn F hF (by omega) i₀ rsv ((m:ℝ)+1) D
    hslo hs1 hθ1 hc hdθ hρlo hρhi hD Allowed hAllowed hthreshold hsclass hclass P hreg π hdegree hnoshort
  refine ⟨i₀,rsv,C,hi,hslo,hs1,hsclass,hclass,hsize,hcard,?_,sampling,w,seed,?_⟩
  · intro u
    convert hreserve u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · exact hmatch
end Oberwolfach
