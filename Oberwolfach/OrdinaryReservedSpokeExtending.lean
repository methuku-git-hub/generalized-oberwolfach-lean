module

public import Oberwolfach.RawReservedSelectedExtendingList
public import Oberwolfach.RawReservedSpokeList
public import Oberwolfach.RawSelectedReferenceDensity
public import Oberwolfach.ExtendingListPhysicalDeletion

@[expose] public section
/-! The selected spoke lists retain their fixed reserve density independently
of the matching error. The same selected physical layer supplies free arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryReservedSpokeExtendingFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_reserved_spoke_extending_lists
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:2≤n)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (γ pstar p smin rsv β lam ζ:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p)
    (hsmin:0≤smin) (hs:smin≤rsv) (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false v y)).card:ℝ))
    (hneighbour:∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>σ (Sum.inr e)) u false
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i).card*rsv|<(n:ℝ)^(3/4:ℝ))
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin)
    (hbudget:(lam+2*ζ)*n≤β*n)
    (Del:SimpleGraph (Fin n)) (hDel:∀x,(Del.degree x:ℝ)≤ζ*n):
    ∀u,IsExtendingList
      (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y)
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) lam :=by
  have hnR:(0:ℝ)≤n:=by positivity
  have hα:0≤γ*pstar^2:=mul_nonneg hγ (sq_nonneg pstar)
  have hdensity:=raw_selected_reference_neighbour_density P π d (fun e=>σ (Sum.inl e)) γ pstar p ((n:ℝ)^(3/4:ℝ)) hγ hpstar hp
    (by simpa using hn) (by simpa using hP) (by simpa using herror) (by simpa using hpaths)
  intro u
  have hprotected:=raw_reserved_selected_neighbour_concentration_extending_list P π d (fun e=>σ (Sum.inl e))
    (fun e=>σ (Sum.inr e)) u false (fun _ _=>rsv) (γ*pstar^2) smin β ((n:ℝ)^(3/4:ℝ))
    hα hsmin hβ hs hdensity (by simpa using hmargin) (by simpa using hneighbour u)
  have hprotected':IsExtendingList (rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)))
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) β:=by
    convert hprotected using 1 <;> congr 1 <;> ext x <;> simp [rawReservedSpokeList,rawIntervalOrdinaryOuter]
  apply extending_list_after_physical_deletion _ Del _ β lam (ζ*n) hlam (by positivity)
    (by simpa using hDel) ?_ hprotected'
  simp only [Fintype.card_fin]
  nlinarith
end Oberwolfach
