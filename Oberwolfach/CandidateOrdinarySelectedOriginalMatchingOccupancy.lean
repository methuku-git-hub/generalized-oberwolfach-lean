module

public import Oberwolfach.CandidateOrdinaryOriginalWeightedMatchingOccupancy
public import Oberwolfach.OrdinarySeedLengthOriginalMargin

@[expose] public section
/-! The original regular host supplies both seed weights and the matching
core on the assigned sampling law, preserving an arbitrary prior event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryCandidateSelectedOriginalOccupancyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_selected_original_weighted_matching_occupancy_candidate
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃m k:ℕ,L≤m ∧ 7≤m ∧ Even (m+1) ∧ m+1=(k+2)*2 ∧
      successorCycleRatio k+α/2≤1/2+α ∧ ∀(K d:ℕ) (hd:2≤d)
      (ρ₀ t ξ ζ smin θhost θ τ:ℝ) (hθhost:1/2≤θhost) (hρ₀:0<ρ₀) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ) (hsmin:0<smin)
      (hθ:0<θ) (hτ:0<τ),∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv c:ℝ) (D:ℕ)
    (hslo:smin≤rsv) (hs1:rsv≤1/100) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d,
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+3*ζ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/c+4*(n:ℝ)^(3/4:ℝ)) ∧
      ∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨m,k,hL,hm,heven,hlen,hratio⟩:=ordinary_seed_length_original_margin L α hα
  refine ⟨m,k,hL,hm,heven,hlen,hratio,?_⟩
  intro K d hd ρ₀ t ξ ζ smin θhost θ τ hθhost hρ₀ ht hξ hζ hsmin hθ hτ
  exact ordinary_original_weighted_matching_occupancy_candidate K d m k hd (by omega) hlen
    ρ₀ t ξ ζ smin θhost α θ τ hρ₀ ht hξ hζ hsmin hθhost hα hθ hτ hratio
end Oberwolfach
