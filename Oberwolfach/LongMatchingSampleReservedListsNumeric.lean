module

public import Oberwolfach.LongMatchingSampleReservedExtending
public import Oberwolfach.LongReservedListAllNumericMargins

@[expose] public section
/-! Choose the reserved-list budgets after the shared error and deletion cap,
then use the tests on one selected matching outcome at every large order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 36000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchingReservedNumericFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matching_sample_reserved_lists_with_numeric_budgets
    (αHost ρ₀:ℝ) (hα:0<αHost) (hρ:0<ρ₀) (m d:ℕ) (hm:0<m) (hd:0<d):
    let β:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
    ∀(εQ ζcap:ℝ),0≤εQ→εQ≤β/32→0<ζcap→1/(100*(m:ℝ))≤β/16→
    ∃lam η ζ:ℝ,0<lam ∧ 0<η ∧ 0<ζ ∧ ζ≤ζcap ∧
    ∃N:ℕ,∀n≥N,2≤n→∀(U:Type) [Fintype U] [DecidableEq U] [Nonempty (Fin n)],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (K:ℕ) (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ρ:ℝ) (hρlo:ρ₀≤ρ)
      (hP:∀x,(1/2+αHost)*n≤(P.degree x:ℝ))
      (mass:MarkedExpandedActualOutcome (U:=U) π d→ℝ)
      (Other:MarkedExpandedActualOutcome (U:=U) π d→Prop),
    (∃z:MarkedExpandedActualOutcome (U:=U) π d,0<mass z ∧
      (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*(ρ*(1/100)/2)^2-(n:ℝ)^(3/4:ℝ)-
        2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)) ∧
      (∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1/100:ℝ)|<(n:ℝ)^(3/4:ℝ)) ∧
      (∀w,|rawIntervalHubStartCount π d false (fun e=>z.1 (Sum.inr e)) w-
        (n:ℝ)*longAssignedIntervalProbability F hF K m θ w false/d|<(n:ℝ)^(3/4:ℝ)/d) ∧ Other z)→
    ∃z:MarkedExpandedActualOutcome (U:=U) π d,0<mass z ∧ Other z ∧
      ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
      ∀(Inner:Finset (Fin n)),(Inner.card:ℝ)≤εQ*n→
      let D:=rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e))
      let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y;
      ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
        (Inner∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) (β/2) := by
  intro β εQ ζcap hε hεcap hζcap hmtrim
  have hβ:0<β:=by dsimp [β];positivity
  obtain ⟨lam,η,ζ,hlam,hη,hζ,hζcap',htrim,N,hN⟩:=
    long_reserved_list_all_numeric_margins αHost ρ₀ hα hρ m d εQ ζcap hε hεcap hζcap hmtrim
  refine ⟨lam,η,ζ,hlam,hη,hζ,hζcap',max N 2,?_⟩
  intro n hn hn2 U _ _ _ F hF K θ hθ hθ1 P π ρ hρlo hP mass Other hSample
  obtain ⟨herror,hmargin,hbudget,hsub⟩:=hN n (by omega)
  have hpstar:(ρ₀/200:ℝ)≤ρ*(1/100)/2:=by linarith
  obtain ⟨z,hMass,hOther,hLists⟩:=long_matching_sample_supplies_reserved_extending_lists hn2 F hF K m d hm hd θ hθ hθ1 P π
    αHost (ρ₀/200) (ρ*(1/100)/2) β lam ζ hα.le (by positivity) hpstar hβ.le hlam.le hζ.le
    hP herror hmargin hbudget mass Other hSample
  refine ⟨z,hMass,hOther,?_⟩
  intro Del hDel Inner hInner
  exact hLists Del hDel Inner (β/2) εQ η (by positivity) hInner hsub htrim
end Oberwolfach
