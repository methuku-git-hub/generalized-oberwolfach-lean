module

public import Oberwolfach.LongSelectedProtectedExtendingLists
public import Oberwolfach.LongActualRawLawParameters
public import Oberwolfach.TwoComponentLower

@[expose] public section
/-! Discharge the selected-list probability and host-density inputs from the
original long-class recipe and regular-host assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSelectedEventDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_selected_extending_lists_from_event
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:2≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowedSet:Allowed.Nonempty) (hvalid:∀s∈Allowed,3≤s)
    (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K m d:ℕ) (hK:0<K) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D αHost:ℝ)
    (hθ:0<θ) (hθmax:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D) (hα:0<αHost)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (Dnat:ℕ) (hreg:P.IsRegularOfDegree Dnat)
    (hmin:(allowedThreshold Allowed+αHost)*n≤(Dnat:ℝ)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (β lam ζ:ℝ) (hβ:0<β) (hlam:0<lam) (hζ:0<ζ)
    (hN:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*θ ∧
      (lam+2*ζ)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n)
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*(ρ*(1/100)/2)^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false v y)).card:ℝ))
    (hneighbour:∀u i,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) u
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i).card*
      (1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑j,longAssignedSpokeProbability F hF K m θ u j))|<(n:ℝ)^(3/4:ℝ))
    (hstarts:∀u g,|rawIntervalHubStartCount π d g (fun e=>σ (Sum.inr e)) u-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Del:SimpleGraph (Fin n)) (hDel:∀x,(Del.degree x:ℝ)≤ζ*n)
    (Pack:Finset (Sym2 (Fin n))) (hPack:Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset):
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    (∀u,IsExtendingList Dfree (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t J u) lam) ∧
    (∀x y,Dfree x y→s(x,y)∉Pack):=by
  intro Dfree
  have hn0:0<n:=by omega
  have hθ1:θ≤1:=by linarith
  have hLaw:=long_assigned_actual_raw_law_parameters hn0 F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ.le hθmax hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hQ:∀u,∑g,longAssignedIntervalProbability F hF K m θ u g≤1/8:=hLaw.2.2.2.2.2.2.2.1
  have hp:ρ₀/200≤ρ*(1/100)/2:=by linarith
  have hhalf:=allowedThreshold_half_le hAllowedSet hvalid
  have hP:∀x,(1/2+αHost)*n≤(P.degree x:ℝ):=by
    intro x
    have hh:=hreg x
    have hnR:(0:ℝ)≤n:=by positivity
    have hmarg:=mul_le_mul_of_nonneg_right (show (1/2+αHost:ℝ)≤allowedThreshold Allowed+αHost by linarith) hnR
    rw [hh]
    exact hmarg.trans hmin
  exact long_selected_protected_extending_lists hn F hF K m d (by omega) (by omega) θ hθ.le hθ1 P π σ t J
    αHost (ρ₀/200) (ρ*(1/100)/2) β lam ζ hα.le (by positivity) hp hβ.le hlam.le hζ.le hP hN.1 hpaths
    hneighbour hstarts hQ hN.2.1 hN.2.2 Del hDel Pack hPack
end Oberwolfach
