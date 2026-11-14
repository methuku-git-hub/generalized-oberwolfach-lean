module

public import Oberwolfach.LongSelectedReservedSpokeExtending
public import Oberwolfach.ReservedSpokeTrimmedWithoutMarkedLoss

@[expose] public section
/-! The retained marked set is disjoint from the reserved labels. Thus its
size does not enter the loss in the extending-list estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_selected_reserved_extending_no_marked_loss
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
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (Inner:Finset (Fin n)) (βfinal ε:ℝ) (hβfinal:0≤βfinal)
    (hInner:(Inner.card:ℝ)≤ε*n) (htrim:βfinal+ε≤lam):
    let D:=rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e))
    let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y;
    ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\
      (Inner∪retainedFinalMarkedAt π d (fun e=>σ (Sum.inr e)) t J u)) βfinal:=by
  intro D Dfree
  have hdec:selectedWitnessFinDecidable_reserved n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [←hdec] at hpaths hneighbour
  obtain ⟨hext,_⟩:=long_selected_reserved_spoke_extending_lists hn F hF K m d hm hd θ hθ hθ1 P π σ
    γ pstar p β lam ζ hγ hpstar hp hβ hlam hζ hP herror hpaths hneighbour hmargin hbudget Del hDel ∅ (by simp)
  rw [hdec] at hext
  have hbudget':βfinal*Fintype.card (Fin n)+Inner.card≤lam*Fintype.card (Fin n):=by
    have hh:=mul_le_mul_of_nonneg_right htrim (show (0:ℝ)≤n by positivity)
    simp only [Fintype.card_fin]
    nlinarith only [hh,hInner]
  exact reserved_spoke_trimmed_without_marked_loss π d (fun e=>σ (Sum.inr e)) t J Dfree Inner lam βfinal hβfinal hbudget' hext
end Oberwolfach
