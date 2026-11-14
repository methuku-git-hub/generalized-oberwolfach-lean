module

public import Oberwolfach.LongOrderedEveryClassSampleTests
public import Oberwolfach.VortexSizeBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_common_event_residual_lists
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (r d Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hε:0≤ε)
    (θ ρ D γList pstarList βList lamList Δ βfinal η:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (hγ:0≤γList) (hp:0≤pstarList) (hpCap:pstarList≤ρ*(1/100)/2)
    (hβ:0≤βList) (hlam:0≤lamList) (hΔ:0≤Δ)
    (hdeg:∀x,(1/2+γList)*n≤(P.degree x:ℝ))
    (hlist1:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstarList^2*n)
    (hlist2:βList*n+(n:ℝ)^(3/4:ℝ)≤γList*pstarList^2*n*(1/100:ℝ))
    (hbudget:(lamList+2*Δ)*n≤βList*n) (hfinal:0≤βfinal)
    (herr:(n:ℝ)^(3/4:ℝ)≤η*n)
    (htrim:βfinal+ε+1/(100*((r+4:ℕ):ℝ))+η≤lamList)
    (hTests:LongOrderedEveryClassSampleTests P π r K d θ ρ D F hF z):
    ∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      ∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
        (rawReservedSpokeList π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) u \
          (Q.extendedVertices 1∪retainedFinalMarkedAt π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e)))
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal :=by
  have hInner:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_upper hε
  intro Del hDel
  exact hTests.2.2 γList pstarList βList lamList Δ hγ hp hpCap hβ hlam hΔ hdeg hlist1 hlist2 hbudget Del hDel
      (Q.extendedVertices 1) βfinal ε η hfinal hInner herr htrim
end Oberwolfach
