module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryRecodedPairsListsOnPrior
public import Oberwolfach.CandidateOrdinaryRecodedListsOnPriorDirectReserve
public import Oberwolfach.CandidateOrdinaryPairAssignmentsPriorDirectReserve
public import Oberwolfach.OrdinaryPlacementRecodedTestsPrior
public import Oberwolfach.CandidateOrdinaryRecodedProtectedListsAfterDeletionDirectReserve

@[expose] public section
/-! The recoded two-path and neighbourhood tests produce the protected
extending lists on an arbitrary earlier event of the same physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) candidateRecodedPairsListsFin_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_recoded_pairs_lists_on_prior_candidate_direct_reserve
    (d:ℕ) (hd:2≤d) (θ ρ₀ χpair χlist:ℝ) (hθ:0<θ) (hθ1:θ≤1/100)
    (hρ₀:0<ρ₀) (hχpair:0<χpair) (hχlist:0<χlist)
    (hda:1/θ≤d) (hspace:1/(4*(d:ℝ))≤5*θ^2/256):
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n≥N,2≤n→∀{U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K m:ℕ) (hK:0<K) (hm:7≤m) (i₀:Fin K) (rsv ρ D:ℝ)
    (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hρlo:ρ₀≤ρ)
    (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hDlo:(n:ℝ)/2≤D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (γ pstar β lam ζ:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hpstarFree:pstar≤p+u/2)
    (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ)
    (hdeg:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤(γ*pstar^2)*n*(θ/2))
    (hbudget:(lam+2*ζ)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤β*n),
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1);
    ∀(hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    (∀z,E z→∀w g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) w-
      (n:ℝ)*q w g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    1-((εE+χpair)+2*χlist)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧ OrdinaryProtectedBadEdgeAssignments π d z.1 a ∧
      ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret)
        (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→∀w,
        IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>z.1 (Sum.inr e)) false true tret Jret w) lam) :=by
  obtain ⟨a,ha,Npair,hpair⟩:=ordinary_assigned_pairs_and_assignments_on_prior_candidate_direct_reserve d hd θ ρ₀ χpair
    hθ hθ1 hρ₀ hχpair hda hspace
  obtain ⟨Nlist,hlist⟩:=ordinary_assigned_recoded_lists_on_prior_candidate_direct_reserve d hd χlist hχlist
  refine ⟨a,ha,max Npair Nlist,?_⟩
  intro n hn hn2 U _ _ hUn F hF Allowed hAllowed K m hK hm i₀ rsv ρ D hrs0 hrs1 hρlo hρ hρ1 hD hDlo hsize hClassReserve
    P π hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum γ pstar β lam ζ hγ hpstar hpstarFree hβ hlam hζ hdeg herror hmargin hbudget
    q s hq hQ hs hS R _ ν E εE μ hE hstarts
  have hc:(8:ℝ)≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  let E':(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop:=fun z=>
    E z ∧ OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧ OrdinaryProtectedBadEdgeAssignments π d z.1 a
  have hE':1-(εE+χpair)≤(μ.sigma ν).probability E':=
    hpair n (by omega) (by omega) F hF K hK i₀ rsv ((m:ℝ)+1) ρ D hrs0 hrs1 hc hρlo hρ hρ1 hD hDlo hsize
      Allowed hAllowed hClassReserve hUn π hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hq hQ hs hS ν E εE hE
  have hstart':∀z,E' z→∀w g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) w-
      (n:ℝ)*q w g/d|<(n:ℝ)^(3/4:ℝ)/d:=fun z hz=>hstarts z hz.1
  have hh:=hlist n (by omega) hn2 hUn F hF Allowed hAllowed K m hK hm i₀ rsv θ ρ D hrs0 hrs1 hθ hθ1 hda hρ hρ1 hD hsize hClassReserve
    P π hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum γ pstar β lam ζ hγ hpstar hpstarFree hβ hlam hζ hdeg herror hmargin hbudget
    hq hQ hs hS ν E' (εE+χpair) hE' hstart'
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1,hz.1.2.1,hz.1.2.2,hz.2⟩
end Oberwolfach
