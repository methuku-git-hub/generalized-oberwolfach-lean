module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinarySelectedProtectedExtendingLists
public import Oberwolfach.OrdinarySelectedProtectedExtendingLists
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedRootCountUpperDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedUnassignedSlackDirectReserve
public import Oberwolfach.RawSelectedNeighbourTestsExtendingList
public import Oberwolfach.RawSelectedReferenceDensity
public import Oberwolfach.OrdinaryAssignedUnassignedSlack
public import Oberwolfach.OrdinaryAssignedRootCountUpper

@[expose] public section
/-! The same sampled neighbourhood and start tests give protected extending
lists for the actual assigned ordinary factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinarySelectedProtectedListsFin_candidate_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_selected_protected_extending_lists_candidate_direct_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:2≤n) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ ρ D:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ω:Sym2 (Fin n)→Fin 6×Bool)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (γ pstar p β lam:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hβ:0≤β) (hlam:0≤lam)
    (hdeg:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤(γ*pstar^2)*n*(θ/2))
    (hbudget:lam*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤β*n)
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (ω e)) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) false v y)).card:ℝ))
    (hcount:∀w i,|rawIntervalUnassignedHubCountOn π d σ w (rawSelectedNeighbourTestSet P π d ω i)-
      (rawSelectedNeighbourTestSet P π d ω i).card*(1-(∑g,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)-
        (∑j,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1) w j))|<(n:ℝ)^(3/4:ℝ))
    (hstarts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    ∀w,IsExtendingList (rawSelectedPhysicalRelation P π d ω)
      (rawIntervalProtectedUnassignedList π d σ false true r Jret w) lam:=by
  have hm8:8≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  have hslack:=ordinary_assigned_unassigned_slack_candidate_direct_reserve (by omega) F hF K hK i₀ rsv θ ((m:ℝ)+1) ρ D d hd
    hrs0 hrs1 hθ hθ1 hm8 hda hρ hρ1 hD hsize Allowed hAllowed hClassReserve
  have hdensity:=raw_selected_reference_neighbour_density P π d ω γ pstar p ((n:ℝ)^(3/4:ℝ)) hγ hpstar hp
    (by simpa using hn) (by simpa only [Fintype.card_fin] using hdeg)
    (by simpa only [Fintype.card_fin] using herror) (by simpa only [Fintype.card_fin] using hpaths)
  intro w
  have hroot0:=ordinary_assigned_root_count_upper_candidate_direct_reserve (by omega) hK m d hm (by omega) F hF Allowed hAllowed i₀ rsv θ
    hrs0 hrs1 hθ hθ1 hClassReserve π σ r
  have hdec:instDecidableEqFin n=ordinarySelectedProtectedListsFin_candidate_direct_reserve n:=Subsingleton.elim _ _
  rw [hdec] at hroot0
  have hroot:=hroot0 Jret w (hstarts w)
  have hrootBudget:lam*(Fintype.card (Fin n):ℝ)+
      (Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):ℝ)≤β*Fintype.card (Fin n):=by
    simp only [Fintype.card_fin]
    linarith
  exact raw_selected_neighbour_concentration_protected_list P π d ω σ false true r Jret w
    (ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1))
    (ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1))
    (γ*pstar^2) (θ/2) β lam ((n:ℝ)^(3/4:ℝ)) (by positivity) (by positivity) hβ hlam
    ((hslack.1 w).1) hdensity (by simpa only [Fintype.card_fin] using hmargin) (by simpa only [Fintype.card_fin] using hcount w) hrootBudget
end Oberwolfach
