module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryOriginalWeightedRecodedLists
public import Oberwolfach.OrdinaryOriginalRegularJointSeedWeights
public import Oberwolfach.CandidateOrdinaryOriginalCoreRecodedListsDirectReserve

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
local instance (priority := high) ordinaryCandidateOriginalWeightedRecodedFin_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_weighted_core_recoded_lists_candidate_direct_reserve
    (K d m k:ℕ) (hd:2≤d) (hm:7≤m) (hlen:m+1=(k+2)*2)
    (ρ₀ t ξ ζ smin χpair χlist θhost α θ τ:ℝ)
    (hρ₀:0<ρ₀) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ) (hsmin:0<smin) (hχpair:0<χpair) (hχlist:0<χlist)
    (hθhost:1/2≤θhost) (hα:0<α) (hθ:0<θ) (hθ1:θ≤1/100) (hda:1/θ≤d)
    (hspace:1/(4*(d:ℝ))≤5*θ^2/256) (hτ:0<τ)
    (hratio:successorCycleRatio k+α/2≤1/2+α):
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n:ℕ,N≤n→2≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv c:ℝ) (D:ℕ)
    (hslo:smin≤rsv) (hs1:rsv≤1/100) (hc:8≤c) (hcEq:c=(m:ℝ)+1)
     (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d,
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
    ∀(γList βList lamList ζDel:ℝ),0≤γList→0≤βList→0≤lamList→0≤ζDel→
    (∀x,(1/2+γList)*n≤(P.degree x:ℝ))→
    (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*(ρ₀*θ/4)^2*n→
    βList*n+(n:ℝ)^(3/4:ℝ)≤(γList*(ρ₀*θ/4)^2)*n*(θ/2)→
    (lamList+2*ζDel)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤βList*n→
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
    1-((εE+3*ζ+χpair)+2*χlist)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/c+4*(n:ℝ)^(3/4:ℝ)) ∧
      (∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) ∧
      OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧ OrdinaryProtectedBadEdgeAssignments π d z.1 a ∧
      ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret)
        (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζDel*n)→∀w,
        IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>z.1 (Sum.inr e)) false true tret Jret w) lamList) :=by
  obtain ⟨BO,hBO,hweights⟩:=ordinary_original_regular_joint_seed_weights K k θhost α θ τ hα hθ hτ hθhost hratio
  obtain ⟨Nweights,hweights⟩:=hweights d
  have hBM:0<successorWeightUpper k (α/4):=(successorWeightConstants_pos k (α/4) (by positivity)).2
  obtain ⟨a,ha,Ncore,hcore⟩:=ordinary_original_regular_core_recoded_lists_candidate_direct_reserve K d m hd hm θ hθ hθ1 hda hspace ρ₀
    (successorWeightUpper k (α/4)) t ξ ζ smin χpair χlist hρ₀ hBM ht hξ hζ hsmin hχpair hχlist BO hBO
  refine ⟨a,ha,max Nweights Ncore,?_⟩
  intro n hn hn2 U _ _ hUn F hF hK i₀ rsv c D hslo hs1 hc hcEq hρlo hρ1 hD
    Allowed hAllowed hthreshold hClassReserve P hreg π hdegree hnoshort
  have hn0:0<n:=by omega
  obtain ⟨sampling,hcore⟩:=hcore n (by omega) hn2 U hUn F hF hK i₀ rsv c D hslo hs1 hc hcEq hρlo hρ1 hD
    Allowed hAllowed hClassReserve
  obtain ⟨w,seed,hweight,hseed⟩:=hweights n (by omega) hn0 U F hF hK Allowed hAllowed hthreshold P π D hreg hdegree
  have hseed':∃seed':(Fin (m+1)→Fin n)→ℝ,
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed':=by
    rw [hlen]
    exact ⟨seed,hseed⟩
  obtain ⟨seed',hseed'⟩:=hseed'
  refine ⟨sampling,w,seed',?_⟩
  intro γList βList lamList ζDel hγList hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList R _ ν E εE p q s p₂ μ wM wO hE
  have hw0:∀i C,0≤w i C:=fun i C=>(hweight i C).1
  have hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i):=fun i C=>(hweight i C).2
  exact hcore P hreg π θhost α hθhost hα hdegree τ (successorWeightLower k (α/4)) seed'
    hseed' w hw0 hwupper hnoshort γList βList lamList ζDel hγList hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList ν E εE hE
end Oberwolfach
