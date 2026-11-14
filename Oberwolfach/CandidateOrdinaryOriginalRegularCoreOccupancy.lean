module

public import Oberwolfach.CandidateOrdinaryCoreOccupancyNeighbourEvent
public import Oberwolfach.OrdinaryAssignedMatchingCoreOnCommonEvent
public import Oberwolfach.CandidateOrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.CandidateOrdinaryAssignedMatchingCoreOnCommonEvent
public import Oberwolfach.OrdinaryRegularTriangleMatchingHostInputs

@[expose] public section
/-! Select the original assigned sampling law and the actual matching-core
probability using only its factor, regular-host and seed hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) candidateOriginalRegularCoreOccupancyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_regular_matching_core_occupancy_candidate
    (K d m:ℕ) (hd:2≤d) (hm:3≤m) (ρ₀ BM t ξ ζ smin:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ) (hsmin:0<smin)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ) (D:ℕ)
    (hslo:smin≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K),
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d,
    ∀(P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (θhost α:ℝ) (hθhost:1/2≤θhost) (hα:0<α)
    (hdegree:(θhost+α)*(n:ℝ)≤D)
    (τ A:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM weight)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (hw0:∀i C,0≤w i C) (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+3*ζ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/c+4*(n:ℝ)^(3/4:ℝ)) ∧
      ∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨N,hmain⟩:=ordinary_assigned_core_occupancy_and_neighbours_on_common_event_candidate K d m hd hm ρ₀ BM t ξ ζ hρ₀ hBM ht hξ hζ BO hBO
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ hUn F hF hK i₀ rsv θ c D hslo hs1 hθ hθ1 hc hda hρlo hρ1 hD
    Allowed hAllowed hsclass hclass
  obtain ⟨sampling⟩:=ordinary_assigned_vortex_exact_sampling_data_candidate hn0 hD F hF Allowed hAllowed K hK i₀ rsv θ c ρ₀ smin d hd
    hρ₀ hρlo hρ1 hsmin hslo hs1 hθ hθ1 hc hda hsclass hclass
  refine ⟨sampling,?_⟩
  intro P hreg π θhost α hθhost hα hdegree τ A weight hw w hw0 hwupper hnoshort R _ ν E εE
    p q s p₂ μ wM wO hE
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDreal]
  have hs0:0≤rsv:=le_of_lt (hsmin.trans_le hslo)
  let v:Fin n:=⟨0,hn0⟩
  have hDn:D≤n:=by
    have hh:=Finset.card_le_univ (P.neighborFinset v)
    simpa [SimpleGraph.card_neighborFinset_eq_degree,hreg v] using hh
  have hDhi:(D:ℝ)≤2*n:=by
    have hh:(D:ℝ)≤n:=by exact_mod_cast hDn
    have hn0':0≤(n:ℝ):=by positivity
    linarith
  have hDlo:(n:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) (show (0:ℝ)≤n by positivity)
    nlinarith only [hh,hdegree]
  exact hmain n hn hn0 U hUn F hF hK i₀ rsv θ c (initialIndexDensity U D) D hs0 hs1 hθ hθ1 hc hda
    hρlo hρ hρ1 hDreal hsize Allowed hAllowed hsclass hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort
    p 0 0 sampling.u sampling.hp (by norm_num) (by norm_num) sampling.hu sampling.hq sampling.hQ sampling.hs sampling.hS
    sampling.hp₂ sampling.hsum ν E εE hE
end Oberwolfach
