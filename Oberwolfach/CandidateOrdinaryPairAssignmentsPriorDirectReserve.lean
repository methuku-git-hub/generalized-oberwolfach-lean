module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryPairAssignmentsPrior
public import Oberwolfach.CandidateOrdinaryAssignedUnassignedPairsStartsDirectReserve
public import Oberwolfach.OrdinaryPairAssignmentCommonEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Add protected pair and bad-edge assignment tests to any prior on the
same original assigned sample, without a premature extending-list budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) candidatePairAssignmentsPriorFin_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_pairs_and_assignments_on_prior_candidate_direct_reserve
    (d:ℕ) (hd:2≤d) (θ ρ₀ χ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (hρ₀:0<ρ₀) (hχ:0<χ)
    (hda:1/θ≤d) (hspace:1/(4*(d:ℝ))≤5*θ^2/256):
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n≥N,0<n→∀{U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv c ρ D:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hc:8≤c) (hρlo:ρ₀≤ρ) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hDlo:(n:ℝ)/2≤D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (hUhi:Fintype.card U≤n) (π:Equiv.Perm (Fin n))
    (hπ:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    ∀(hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (hs:∀w j,0≤s w j) (hSc:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hSc);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+χ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧ OrdinaryProtectedBadEdgeAssignments π d z.1 a) :=by
  obtain ⟨a,ha,Nassign,hassign⟩:=ordinary_bad_edge_assignment_from_pair_event θ ρ₀ hθ hρ₀ d (by omega) hspace
  obtain ⟨Npair,hpair⟩:=ordinary_assigned_unassigned_pairs_starts_candidate_direct_reserve d hd θ χ hθ hθ1 hχ hda
  refine ⟨a,ha,max Nassign Npair,?_⟩
  intro n hn hn0 U _ _ F hF K hK i₀ rsv c ρ D hs0 hs1 hc hρlo hρ hρ1 hD hDlo hsize S hS hClassReserve hUhi π hπ
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q s hq hQ hs hSc R _ ν E εE μ hE
  let Pair:=fun z:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)=>
    OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1
  have hpairs:1-χ≤(μ.sigma ν).probability Pair:=hpair n (by omega) hn0 F hF K hK i₀ rsv c ρ D
    hs0 hs1 hc hρ hρ1 hD hsize S hS hClassReserve hUhi π hπ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hq hQ hs hSc ν
  have hh:=finiteLaw_intersection_lower (μ.sigma ν) E Pair εE χ hE hpairs
  have hjoined:1-(εE+χ)≤(μ.sigma ν).probability (fun z=>E z ∧ Pair z):=by linarith [hh]
  apply hjoined.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1,hz.2,hassign n (by omega) hn0 U ρ D hρlo hD hDlo hsize π z.1 q hQ hz.2⟩
end Oberwolfach
