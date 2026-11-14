module

public import Oberwolfach.RawSelectedReferenceDensity
public import Oberwolfach.LongAssignedUnassignedSlack
public import Oberwolfach.RetainedRawEndpointCount
public import Oberwolfach.ExtendingListPhysicalDeletion
public import Oberwolfach.SelectedHostAvoidsApproximatePacking

@[expose] public section
/-! Construct the actual protected lists for the selected free host from the
same sample's two-path, unassigned-count, and start-count events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedWitnessFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_selected_protected_extending_lists
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:2≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (γ pstar p β lam ζ:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p)
    (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
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
    (hQ:∀u,∑g,longAssignedIntervalProbability F hF K m θ u g≤1/8)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*θ)
    (hbudget:(lam+2*ζ)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n)
    (Del:SimpleGraph (Fin n)) (hDel:∀x,(Del.degree x:ℝ)≤ζ*n)
    (Pack:Finset (Sym2 (Fin n))) (hPack:Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset):
    let D:=rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e))
    let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y
    (∀u,IsExtendingList Dfree (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t J u) lam) ∧
    (∀x y,Dfree x y→s(x,y)∉Pack):=by
  intro D Dfree
  have hn0:0<n:=by omega
  have hnR:(0:ℝ)≤n:=by positivity
  have hα:0≤γ*pstar^2:=mul_nonneg hγ (sq_nonneg pstar)
  have hdensity:=raw_selected_reference_neighbour_density P π d (fun e=>σ (Sum.inl e)) γ pstar p ((n:ℝ)^(3/4:ℝ)) hγ hpstar hp
    (by simpa using hn) (by simpa using hP) (by simpa using herror) (by simpa using hpaths)
  constructor
  · intro u
    have hprob:=long_assigned_unassigned_probability_at_least_theta hn0 F hF K m hm θ hθ1 u
    have hcount:=retained_raw_endpoint_count_from_start_counts π d hd (fun e=>σ (Sum.inr e)) t J u
      (longAssignedIntervalProbability F hF K m θ) (hQ u) (by simpa using hstarts u)
    have hindex:(lam+2*ζ)*Fintype.card (Fin n)+(Fintype.card (retainedAndRawIntervalIndex π d (fun e=>σ (Sum.inr e)) false true t J u):ℝ)≤β*Fintype.card (Fin n):=by
      simp only [Fintype.card_fin] at *
      linarith
    have hprotected:=raw_selected_neighbour_concentration_protected_list P π d (fun e=>σ (Sum.inl e))
      (fun e=>σ (Sum.inr e)) false true t J u (longAssignedIntervalProbability F hF K m θ)
      (longAssignedSpokeProbability F hF K m θ) (γ*pstar^2) θ β (lam+2*ζ) ((n:ℝ)^(3/4:ℝ))
      hα hθ hβ (by positivity) hprob hdensity (by simpa using hmargin) (by simpa using hneighbour u) hindex
    apply extending_list_after_physical_deletion D Del _ (lam+2*ζ) lam (ζ*n) hlam (by positivity)
      (by simpa using hDel) ?_ (by simpa [D] using hprotected)
    simp only [Fintype.card_fin]
    nlinarith
  · intro x y hxy
    exact selected_host_avoids_approximate_packing P π d σ Pack hPack x y hxy.1
end Oberwolfach
