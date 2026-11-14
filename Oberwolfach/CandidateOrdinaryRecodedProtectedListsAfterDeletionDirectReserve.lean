module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryRecodedProtectedListsAfterDeletion
public import Oberwolfach.OrdinaryPlacementRecodeTarget
public import Oberwolfach.OrdinarySelectedProtectedListsAfterDeletion
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedRootCountUpperDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedUnassignedSlackDirectReserve
public import Oberwolfach.CandidateOrdinarySelectedProtectedExtendingListsDirectReserve
public import Oberwolfach.OrdinarySelectedProtectedExtendingLists
public import Oberwolfach.ExtendingListPhysicalDeletion
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
local instance ordinaryRecodedProtectedDeletionFin_candidate_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_recoded_protected_lists_after_deletion_candidate_direct_reserve
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
    (γ pstar p β lam ζ:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ)
    (hdeg:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤(γ*pstar^2)*n*(θ/2))
    (hbudget:(lam+2*ζ)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤β*n)
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (ordinaryPlacementColourRecode (ω e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ordinaryPlacementColourRecode (ω e))) false v y)).card:ℝ))
    (hcount:∀w i,|rawIntervalUnassignedHubCountOn π d σ w (rawSelectedNeighbourTestSet P π d (fun e=>ordinaryPlacementColourRecode (ω e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>ordinaryPlacementColourRecode (ω e)) i).card*(1-(∑g,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)-
        (∑j,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1) w j))|<(n:ℝ)^(3/4:ℝ))
    (hstarts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
    ∀w,IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d ω x y ∧ ¬Del.Adj x y)
      (rawIntervalProtectedUnassignedList π d σ false true r Jret w) lam:=by
  intro Del hDel w
  have hbase:=ordinary_assigned_selected_protected_extending_lists_candidate_direct_reserve hn hK m d hm hd F hF Allowed hAllowed i₀ rsv θ ρ D
    hrs0 hrs1 hθ hθ1 hda hρ hρ1 hD hsize hClassReserve P π (fun e=>ordinaryPlacementColourRecode (ω e)) σ r Jret γ pstar p β (lam+2*ζ)
    hγ hpstar hp hβ (by positivity) hdeg herror hmargin hbudget hpaths hcount hstarts w
  apply extending_list_after_physical_deletion (ordinaryPlacementPhysicalRelation P π d ω) Del _ (lam+2*ζ) lam (ζ*n) hlam (by positivity)
    (by simpa only [Fintype.card_fin] using hDel) ?_ hbase
  simp only [Fintype.card_fin]
  nlinarith
end Oberwolfach
