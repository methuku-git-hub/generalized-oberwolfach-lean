module

public import Oberwolfach.CandidateOrdinarySelectedWeightedRecodedListsNormalizedDirectReserve
public import Oberwolfach.CandidateOrdinarySelectedWeightedRecodedListsDirectReserve
public import Oberwolfach.OrdinaryRecodedAbundanceIndependentReserveSelection

@[expose] public section
/-! Choose the seed, recoded-list rates, spacing and abundant reservation in
order, and retain matching, assignments and extending lists on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_recoded_abundance_matching_event_independent_reserve_with_normalization
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hρ₀:0<ρ₀) (hα:0<α):
    ∃m k:ℕ,L≤m ∧ 7≤m ∧ Even (m+1) ∧ m+1=(k+2)*2 ∧
      successorCycleRatio k+α/2≤1/2+α ∧
    ∀θ:ℝ,0<θ→θ≤1/100→
    ∃βList lamList ζDel smin:ℝ,0<βList ∧ βList≤1 ∧ 0<lamList ∧ 0<ζDel ∧ 0<smin ∧ smin=βfreq/200 ∧
    ∀dNeed:ℕ,∃d K rank:ℕ,dNeed≤d ∧ 2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤βfreq ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∀(hd' : 2≤d) (θhost:ℝ),1/2≤θhost→
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧
    ∀τ:ℝ,0<τ→∀(t ξ ζ χpair χlist:ℝ),0<t→0<ξ→0<ζ→0<χpair→0<χlist→
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n:ℕ,N≤n→2≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2),
    (∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))→
    ∀(D:ℕ),0<D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    ∀(Allowed:Set ℕ), (∀u,AllowedCycleLengths (F u) Allowed)→
      (∀r∈Allowed,cycleThreshold r≤θhost)→
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→
    ∀(π:Equiv.Perm (Fin n)),(θhost+α)*(n:ℝ)≤D→
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∃(i₀:Fin K) (rsv:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=rstar ∧ smin≤rsv ∧ rsv≤1/100 ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=rstar) ∧
      (∀u,(rstar:ℝ)*(C u).card=rsv*n) ∧
      (∀u,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n) ∧
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d,
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
    (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
    (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) ∧
    (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
    SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
      (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed ∧
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
    1-((εE+3*ζ+χpair)+2*χlist)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/((m:ℝ)+1)+4*(n:ℝ)^(3/4:ℝ)) ∧
      (∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) ∧
      OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧ OrdinaryProtectedBadEdgeAssignments π d z.1 a ∧
      ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret)
        (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζDel*n)→∀w,
        IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>z.1 (Sum.inr e)) false true tret Jret w) lamList)  :=by
  obtain ⟨m,k,hL,hm,heven,hlen,hratio,hcore⟩:=ordinary_selected_original_weighted_recoded_lists_with_normalization_candidate_direct_reserve L α hα
  refine ⟨m,k,hL,hm,heven,hlen,hratio,?_⟩
  intro θ hθ hθ1
  obtain ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlam,hζDel,hsmin,hsminEq,hsel⟩:=
    ordinary_recoded_abundance_independent_reserve_selection βfreq θ ρ₀ (α/2) hβfreq hβ1 hθ hρ₀ (by positivity) rstar m hr
  refine ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlam,hζDel,hsmin,hsminEq,?_⟩
  intro dNeed
  obtain ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,Nsel,hsel⟩:=hsel dNeed
  refine ⟨d,K,rank,hdNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,?_⟩
  intro hd' θhost hθhost
  obtain ⟨BO,hBO,hcore⟩:=hcore K d hd ρ₀ smin θhost θ
    hθhost hρ₀ hsmin hθ hθ1 hdθ hspace
  refine ⟨BO,hBO,?_⟩
  intro τ hτ t ξ ζ χpair χlist ht hξ hζ hχpair hχlist
  obtain ⟨a,ha,Ncore,hcore⟩:=hcore τ hτ t ξ ζ χpair χlist ht hξ hζ hχpair hχlist
  refine ⟨a,ha,max Nsel Ncore,?_⟩
  intro n hn hn2 U _ _ hUn F hF hfreq D hD hρlo hρhi Allowed hAllowed hthreshold P hreg π hdegree hnoshort
  obtain ⟨herror,hmargin,hbudget,hres⟩:=hsel n (by omega)
  obtain ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,hreserve⟩:=hres U F hF hfreq
  have hc:(8:ℝ)≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  have hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv:=by
    convert hreserve using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  obtain ⟨sampling,w,seed,hweight,hNorm,hzero,hseed,hmatch⟩:=hcore n (by omega) hn2 U hUn F hF (by omega) i₀ rsv ((m:ℝ)+1) D
    hslo hs1 hc rfl hρlo hρhi hD Allowed hAllowed hthreshold hClassReserve P hreg π hdegree hnoshort
  have hdeg:∀x,(1/2+α/2)*n≤(P.degree x:ℝ):=by
    intro x
    rw [hreg x]
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)+α/2≤θhost+α by linarith) (show (0:ℝ)≤n by positivity)
    exact hh.trans hdegree
  refine ⟨i₀,rsv,C,hi,hslo,hs1,hclass,hsize,hcard,?_,sampling,w,seed,hweight,hNorm,hzero,hseed,?_⟩
  · intro u
    convert hreserve u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · exact hmatch (α/2) βList lamList ζDel (by positivity) hβList.le hlam.le hζDel.le hdeg herror hmargin hbudget
end Oberwolfach
