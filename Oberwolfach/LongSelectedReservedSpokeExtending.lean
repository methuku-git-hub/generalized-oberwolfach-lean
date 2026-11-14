module

public import Oberwolfach.RawReservedSelectedExtendingList
public import Oberwolfach.RawReservedSpokeList
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
local instance selectedWitnessFinDecidable_reserved (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_selected_reserved_spoke_extending_lists
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:2≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    
    (γ pstar p β lam ζ:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p)
    (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false v y)).card:ℝ))
    (hneighbour:∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>σ (Sum.inr e)) u false
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i).card*(1/100:ℝ)|<(n:ℝ)^(3/4:ℝ))
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*(1/100:ℝ))
    (hbudget:(lam+2*ζ)*n≤β*n)
    (Del:SimpleGraph (Fin n)) (hDel:∀x,(Del.degree x:ℝ)≤ζ*n)
    (Pack:Finset (Sym2 (Fin n))) (hPack:Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset):
    let D:=rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e))
    let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y
    (∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) lam) ∧
    (∀x y,Dfree x y→s(x,y)∉Pack):=by
  intro D Dfree
  have hn0:0<n:=by omega
  have hnR:(0:ℝ)≤n:=by positivity
  have hα:0≤γ*pstar^2:=mul_nonneg hγ (sq_nonneg pstar)
  have hdensity:=raw_selected_reference_neighbour_density P π d (fun e=>σ (Sum.inl e)) γ pstar p ((n:ℝ)^(3/4:ℝ)) hγ hpstar hp
    (by simpa using hn) (by simpa using hP) (by simpa using herror) (by simpa using hpaths)
  constructor
  · intro u
    have hprotected:=raw_reserved_selected_neighbour_concentration_extending_list P π d (fun e=>σ (Sum.inl e))
      (fun e=>σ (Sum.inr e)) u false (fun _ _=>(1/100:ℝ)) (γ*pstar^2) (1/100) β ((n:ℝ)^(3/4:ℝ))
      hα (by norm_num) hβ (by norm_num) hdensity (by simpa using hmargin) (by simpa using hneighbour u)
    have hprotected':IsExtendingList D (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) β:=by
      convert hprotected using 1 <;> congr 1 <;> ext x <;> simp [D,rawReservedSpokeList,rawIntervalOrdinaryOuter]
    apply extending_list_after_physical_deletion D Del _ β lam (ζ*n) hlam (by positivity)
      (by simpa using hDel) ?_ hprotected'
    simp only [Fintype.card_fin]
    nlinarith
  · intro x y hxy
    exact selected_host_avoids_approximate_packing P π d σ Pack hPack x y hxy.1
end Oberwolfach
