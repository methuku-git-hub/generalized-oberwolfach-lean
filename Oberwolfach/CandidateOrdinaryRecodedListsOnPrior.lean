module

public import Oberwolfach.OrdinaryPlacementRecodedTestsPrior
public import Oberwolfach.CandidateOrdinaryRecodedProtectedListsAfterDeletion

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
local instance (priority := high) candidateRecodedListsOnPriorFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_recoded_lists_on_prior_candidate
    (d:ℕ) (hd:2≤d) (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,∀n≥N,2≤n→∀{U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K m:ℕ) (hK:0<K) (hm:7≤m) (i₀:Fin K) (rsv θ ρ D:ℝ)
    (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K)
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
    1-(εE+2*χ)≤(μ.sigma ν).probability (fun z=>E z ∧
      ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret)
        (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→∀w,
        IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>z.1 (Sum.inr e)) false true tret Jret w) lam) :=by
  obtain ⟨N,hN⟩:=ordinary_placement_recoded_tests_and_prior d hd χ hχ
  refine ⟨N,?_⟩
  intro n hn hn2 U _ _ hUn F hF Allowed hAllowed K m hK hm i₀ rsv θ ρ D hrs0 hrs1 hθ hθ1 hda hρ hρ1 hD hsize hrsclass hclass
    P π hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum γ pstar β lam ζ hγ hpstar hpstarFree hβ hlam hζ hdeg herror hmargin hbudget
    q s hq hQ hs hS R _ ν E εE μ hE hstarts
  have htests:=hN (Fin n) U Bool Bool (by simpa using hn) (by simpa using hUn) P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort ν E εE hE
  apply htests.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  intro tret Jret Del hDel
  have hpaths:=hz.2.1
  have hcounts:=hz.2.2
  apply ordinary_assigned_recoded_protected_lists_after_deletion_candidate hn2 hK m d hm hd F hF Allowed hAllowed i₀ rsv θ ρ D
    hrs0 hrs1 hθ hθ1 hda hρ hρ1 hD hsize hrsclass hclass P π (fun e=>z.1 (Sum.inl e)) (fun e=>z.1 (Sum.inr e))
    tret Jret γ pstar (p+u/2) β lam ζ hγ hpstar hpstarFree hβ hlam hζ hdeg herror hmargin hbudget
  · simpa only [ordinaryPlacementWheelRecode,Fintype.card_fin] using hpaths
  · simp only [ordinaryPlacementWheelRecode,id_eq,q,s,Fintype.card_fin] at hcounts
    intro w i
    convert hcounts w i using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · exact hstarts z hz.1
  · exact hDel
end Oberwolfach
