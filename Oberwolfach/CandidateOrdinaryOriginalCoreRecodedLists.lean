module

public import Oberwolfach.CandidateOrdinaryOriginalRegularCoreOccupancy
public import Oberwolfach.CandidateOrdinaryRecodedPairsListsOnPrior
public import Oberwolfach.CandidateOrdinaryRecodedFreeProbabilityLower
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
local instance (priority := high) candidateOriginalCoreRecodedListsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_regular_core_recoded_lists_candidate
    (K d m:ℕ) (hd:2≤d) (hm:7≤m) (θ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100)
    (hda:1/θ≤d) (hspace:1/(4*(d:ℝ))≤5*θ^2/256)
    (ρ₀ BM t ξ ζ smin χpair χlist:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ) (hsmin:0<smin)
    (hχpair:0<χpair) (hχlist:0<χlist)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i):
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n:ℕ,N≤n→2≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv c:ℝ) (D:ℕ)
    (hslo:smin≤rsv) (hs1:rsv≤1/100) (hc:8≤c) (hcEq:c=(m:ℝ)+1)
     (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
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
    (γ βList lamList ζDel:ℝ) (hγ:0≤γ) (hβ:0≤βList) (hlam:0≤lamList) (hζDel:0≤ζDel)
    (hdeg:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*(ρ₀*θ/4)^2*n)
    (hmargin:βList*n+(n:ℝ)^(3/4:ℝ)≤(γ*(ρ₀*θ/4)^2)*n*(θ/2))
    (hbudget:(lamList+2*ζDel)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤βList*n)
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
  obtain ⟨Ncore,hcore⟩:=ordinary_original_regular_matching_core_occupancy_candidate K d m hd (by omega) ρ₀ BM t ξ ζ smin
    hρ₀ hBM ht hξ hζ hsmin BO hBO
  obtain ⟨a,ha,Nlist,hlist⟩:=ordinary_assigned_recoded_pairs_lists_on_prior_candidate d hd θ ρ₀ χpair χlist
    hθ hθ1 hρ₀ hχpair hχlist hda hspace
  refine ⟨a,ha,max Ncore Nlist,?_⟩
  intro n hn hn2 U _ _ hUn F hF hK i₀ rsv c D hslo hs1 hc hcEq hρlo hρ1 hD Allowed hAllowed hsclass hclass
  obtain ⟨sampling,hcore⟩:=hcore n (by omega) (by omega) U hUn F hF hK i₀ rsv θ c D
    hslo hs1 hθ hθ1 hc hda hρlo hρ1 hD Allowed hAllowed hsclass hclass
  refine ⟨sampling,?_⟩
  intro P hreg π θhost α hθhost hα hdegree τ A weight hw w hw0 hwupper hnoshort
    γ βList lamList ζDel hγ hβ hlam hζDel hdeg herror hmargin hbudget R _ ν E εE p q s p₂ μ wM wO hE
  subst c
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDreal]
  have hs0:0≤rsv:=(hsmin.trans_le hslo).le
  have hDlo:(n:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) (show (0:ℝ)≤n by positivity)
    nlinarith only [hh,hdegree]
  have hpfree:ρ₀*θ/4≤p+sampling.u/2:=by
    dsimp [p]
    exact ordinary_assigned_recoded_free_probability_lower_candidate (by omega) hD F hF Allowed hAllowed K hK i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d hd
      hρ₀ hρlo hρ1 hsmin hslo hs1 hθ hθ1 hc hda hsclass hclass sampling
  let Prior:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop:=fun z=>
    E z ∧ OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/((m:ℝ)+1)+4*(n:ℝ)^(3/4:ℝ)) ∧
      ∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)
  have hPrior:1-(εE+3*ζ)≤(μ.sigma ν).probability Prior:=
    hcore P hreg π θhost α hθhost hα hdegree τ A weight hw w hw0 hwupper hnoshort ν E εE hE
  have hstarts:∀z,Prior z→∀w g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) w-
      (n:ℝ)*q w g/d|<(n:ℝ)^(3/4:ℝ)/d:=by
    intro z hz w g
    have hh:=hz.2.1.2.2.2 w g
    simp only [rawExpandedApproximateCollapse,id_eq] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hpstar0:0≤ρ₀*θ/4:=by positivity
  have hh:=hlist n (by omega) hn2 hUn F hF Allowed hAllowed K m hK hm i₀ rsv (initialIndexDensity U D) D
    hs0 hs1 hρlo hρ hρ1 hDreal hDlo hsize hsclass hclass P π hnoshort p 0 p₂ 0 sampling.u
    sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    γ (ρ₀*θ/4) βList lamList ζDel hγ hpstar0 hpfree hβ hlam hζDel hdeg herror hmargin hbudget
    sampling.hq sampling.hQ sampling.hs sampling.hS ν Prior (εE+3*ζ) hPrior hstarts
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1,hz.1.2.1,hz.1.2.2.1,hz.1.2.2.2,hz.2.1,hz.2.2.1,hz.2.2.2⟩
end Oberwolfach
