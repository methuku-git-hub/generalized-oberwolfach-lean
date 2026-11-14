module

public import Oberwolfach.LongFirstPrescribedMatchingAlignedPack
public import Oberwolfach.LongSelectedAlignedSourceWithLoad

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassPrescribedNoMarkedFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def FirstVortexClassPrescribedAssignmentNoMarkedBudget
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S Del Used Kbad:SimpleGraph (Fin n)) (I:Finset (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (H:Finset U) (α b ρ₀ θ ε lam:ℝ)
    (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n))):Prop:=
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let Jbad:=spanningRestriction (S\Used) I\Kbad
    let ρ:=ρ₀/4
    (∀v,(Kbad.degree v:ℝ)≤(α/16)*n) ∧
    (Kbad.edgeFinset.card:ℝ)≤(θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n ∧
    Disjoint Kbad.edgeFinset Pack ∧
    (∀v,(Jbad.degree v:ℝ)≤ε*n) ∧ Disjoint Kbad.edgeFinset Jbad.edgeFinset ∧
    Disjoint Used.edgeFinset Jbad.edgeFinset ∧
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
    let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
    (∀e,Disjoint (Lbad e) H) ∧
    (∀w e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old w→w∈Lbad e→w∈Bad v) ∧
    (∀e∈Kbad.edgeFinset,(ρ/40000)*n≤((Lbad e).card:ℝ)) ∧
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
    let Kload:=⌈4*(Kbad.edgeFinset.card:ℝ)/((ρ/40000)*n)⌉₊
    ∃(assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n),
      (∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e ∧ Dstar (orient e).1 (orient e).2) ∧
      (∀e∈Kbad.edgeFinset,assign e∈Lbad e ∧ ∀v∈e.toFinset,assign e∉Bad v) ∧
      (∀e∈Kbad.edgeFinset,∀e'∈Kbad.edgeFinset,e≠e'→assign e=assign e'→Disjoint e.toFinset e'.toFinset) ∧
      (∀w,(Kbad.edgeFinset.filter (fun e=>assign e=w)).card≤Kload) ∧
      (∀w,Disjoint (Old w) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w))) ∧
      (∀w,w∈H→prescribedAssignedArcs Kbad assign orient w=∅) ∧
      (∀w,IsPrescribedOrientedMatching (prescribedAssignedArcs Kbad assign orient w)) ∧
      (∀w,(prescribedAssignedArcs Kbad assign orient w).card≤Kload)
end Oberwolfach
