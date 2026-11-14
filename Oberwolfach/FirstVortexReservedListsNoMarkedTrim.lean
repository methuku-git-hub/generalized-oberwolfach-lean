module

public import Oberwolfach.ReservedSpokeAvoidsRetainedMarked
public import Oberwolfach.ReservedSpokeExtendingAfterExclusions
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

theorem first_vortex_reserved_lists_without_marked_loss
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
    (βfinal:ℝ) (hβfinal:0≤βfinal)
    (htrim:βfinal+εQ≤lam):
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
  have hdec:selectedWitnessFinDecidable_reserved n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [←hdec] at hpaths hneighbour
  obtain ⟨hext,_⟩:=long_selected_reserved_spoke_extending_lists hn F hF K m d hm hd θ hθ hθ1 P π σ
    γ pstar p β lam ζ hγ hpstar hp hβ hlam hζ hP herror hpaths hneighbour hmargin hbudget Del hDel' ∅ (Finset.empty_subset _)
  rw [hdec] at hext
  intro w
  have hBudget:βfinal*Fintype.card (Fin n)+(Vort.extendedVertices 1).card+(∅:Finset (Fin n)).card≤lam*Fintype.card (Fin n):=by
    simp only [Fintype.card_fin,Finset.card_empty,Nat.cast_zero,add_zero]
    have hh:=mul_le_mul_of_nonneg_right htrim (Nat.cast_nonneg n)
    nlinarith
  have htrimmed:=extending_list_after_two_exclusions Dfree (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w)
    (Vort.extendedVertices 1) ∅ lam βfinal hβfinal hBudget (hext w)
  have hdis:=reserved_spoke_avoids_retained_marked π d (fun e=>σ (Sum.inr e)) t J w
  have heq:rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w\
      (Vort.extendedVertices 1∪retainedFinalMarkedAt π d (fun e=>σ (Sum.inr e)) t J w)=
      rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w\(Vort.extendedVertices 1∪∅):=by
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_union,Finset.notMem_empty,or_false]
    constructor
    · intro hv; exact ⟨hv.1,by tauto⟩
    · intro hv
      refine ⟨hv.1,?_⟩
      intro hx
      rcases hx with hi|hm
      · exact hv.2 hi
      · exact Finset.disjoint_left.mp hdis hv.1 hm
  rw [heq]
  exact htrimmed

end Oberwolfach
