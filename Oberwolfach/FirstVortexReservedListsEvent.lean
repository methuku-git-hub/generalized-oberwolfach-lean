module

public import Oberwolfach.LongSelectedTrimmedReservedExtending
public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_reserved_lists_from_event_tests
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:2≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (βQ εQ:ℝ) (Vort:Vortex U P Dv βQ εQ mm) (hεQ:0≤εQ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    
    (γ pstar p β lam ζ Δ:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p)
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
    (hΔζ:Δ≤ζ)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (hstarts:∀w,|rawIntervalHubStartCount π d false (fun e=>σ (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w false/d|<(n:ℝ)^(3/4:ℝ)/d)
    (βfinal η:ℝ) (hβfinal:0≤βfinal) (hsub:(n:ℝ)^(3/4:ℝ)≤η*n)
    (htrim:βfinal+εQ+1/(100*(m:ℝ))+η≤lam):
    ∀Del:SimpleGraph (Fin n),(∀x,(Del.degree x:ℝ)≤Δ*n)→
    let D:=rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e))
    let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y
    (∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\
      (Vort.extendedVertices 1∪retainedFinalMarkedAt π d (fun e=>σ (Sum.inr e)) t J u)) βfinal):=by
  intro Del hDel D Dfree
  have hDel':∀x,(Del.degree x:ℝ)≤ζ*n:=by
    intro x
    exact (hDel x).trans (mul_le_mul_of_nonneg_right hΔζ (Nat.cast_nonneg n))
  have hInner:((Vort.extendedVertices 1).card:ℝ)≤εQ*n:=by
    simpa only [Fintype.card_fin] using Vort.first_inner_vertex_size_upper hεQ
  exact long_selected_trimmed_reserved_extending hn F hF K m d hm hd θ hθ hθ1 P π σ
    γ pstar p β lam ζ hγ hpstar hp hβ hlam hζ hP herror hpaths hneighbour hmargin hbudget
    Del hDel' t J hstarts (Vort.extendedVertices 1) βfinal εQ η hβfinal hInner hsub htrim
end Oberwolfach
