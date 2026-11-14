module

public import Oberwolfach.LongSelectedTrimmedReservedExtending
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! Use the reserved-label tests on the selected expanded matching outcome.
Any accompanying correction, chain and matching continuation is retained in
`Other`, while the extending lists are valid after every permitted deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchingReservedExtendingFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

theorem long_matching_sample_supplies_reserved_extending_lists
    (hn:2≤n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (γ pstar p β lam ζ:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p)
    (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*(1/100:ℝ))
    (hbudget:(lam+2*ζ)*n≤β*n)
    (mass:MarkedExpandedActualOutcome (U:=U) π d→ℝ)
    (Other:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (hSample:∃z:MarkedExpandedActualOutcome (U:=U) π d,0<mass z ∧
      (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
        2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)) ∧
      (∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1/100:ℝ)|<(n:ℝ)^(3/4:ℝ)) ∧
      (∀w,|rawIntervalHubStartCount π d false (fun e=>z.1 (Sum.inr e)) w-
        (n:ℝ)*longAssignedIntervalProbability F hF K m θ w false/d|<(n:ℝ)^(3/4:ℝ)/d) ∧ Other z):
    ∃z:MarkedExpandedActualOutcome (U:=U) π d,0<mass z ∧ Other z ∧
      ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
      ∀(Inner:Finset (Fin n)) (βfinal ε η:ℝ),0≤βfinal→
      (Inner.card:ℝ)≤ε*n→(n:ℝ)^(3/4:ℝ)≤η*n→
      βfinal+ε+1/(100*(m:ℝ))+η≤lam→
      let D:=rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e))
      let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y
      ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
        (Inner∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal := by
  obtain ⟨z,hMass,hpaths,hreserved,hstarts,hOther⟩:=hSample
  refine ⟨z,hMass,hOther,?_⟩
  intro Del hDel Inner βfinal ε η hβfinal hInner hsub htrim
  have hdec:(Classical.decEq (Fin n))=instDecidableEqFin n:=Subsingleton.elim _ _
  have hGeneral:=@long_selected_trimmed_reserved_extending n U inferInstance inferInstance
  rw [←hdec] at hGeneral
  exact hGeneral hn F hF K m d hm hd θ hθ hθ1 P π z.1
    γ pstar p β lam ζ hγ hpstar hp hβ hlam hζ hP herror hpaths hreserved hmargin hbudget
    Del hDel _ z.2 hstarts Inner βfinal ε η hβfinal hInner hsub htrim
end Oberwolfach
