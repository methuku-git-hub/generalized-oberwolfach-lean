module

public import Oberwolfach.LongEveryClassEventFromOrderedTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

def LongOrderedEveryClassSampleTests
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (r K d:ℕ)
    (θ ρ D:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (z:MarkedExpandedActualOutcome (U:=U) π d):Prop :=
    let ω:=z.1
    let p:=ρ*(1/100)/2
    let s:ℝ:=(1/100)/(((r+4):ℕ):ℝ)
    let k:=ρ*s/2
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D;
    (∀j v,|((∑w,sampledColourOrientation P (fun e=>ω (Sum.inl e)) j v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun w=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x w ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false w y)).card:ℝ)) ∧
    (∀(γList pstarList βList lamList ζList:ℝ),
          0≤γList→0≤pstarList→pstarList≤ρ*(1/100)/2→0≤βList→0≤lamList→0≤ζList→
          (∀x,(1/2+γList)*n≤(P.degree x:ℝ))→
          (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstarList^2*n→
          βList*n+(n:ℝ)^(3/4:ℝ)≤γList*pstarList^2*n*(1/100:ℝ)→
          (lamList+2*ζList)*n≤βList*n→
          ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζList*n)→
          ∀(Inner:Finset (Fin n)) (βfinal εInner η:ℝ),0≤βfinal→
          (Inner.card:ℝ)≤εInner*n→(n:ℝ)^(3/4:ℝ)≤η*n→
          βfinal+εInner+1/(100*((r+4:ℕ):ℝ))+η≤lamList→
          let D:=rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e))
          let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y;
          ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
            (Inner∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal)
end Oberwolfach
