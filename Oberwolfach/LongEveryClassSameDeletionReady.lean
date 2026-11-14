module

public import Oberwolfach.LongEveryClassMatchingResult

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance everyClassReadyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def LongClassMatchingDeletionWitness
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (K:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)):Prop:=
    let V:=Fin n
    let ω:=z.1
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let Z:=spanningRestriction (⊤:SimpleGraph V) T
    let A:=markedResourceRimGraph C
    (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
    (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
    (markedSampleArcSetGraph P π d raw D₀.arcs)≤Del ∧
    ((longPhysicalStateGraph P ω {0,1,2,3,4})\S)≤Del ∧
    orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
    (∀v,(Del.degree v:ℝ)≤Δ*n) ∧
    (∀x y,Del.Adj x y→¬(Z⊔A).Adj x y) ∧
    (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
    (∀Kbad:SimpleGraph V,Kbad≤S→∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
    (∀x y,M x y=1→P.Adj x y) ∧
    (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1) ∧
    LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z T Del

theorem long_every_class_same_deletion_ready
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (K:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hClass:LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξClass z T K θ D alpha γ eps βList F hF weight w D₀ C)
    (Ready:SimpleGraph (Fin n)→SimpleGraph (Fin n)→Prop)
    (hReady:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈T,∀y∈T,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      ∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→Ready S Del):
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈T,∀y∈T,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
      (∀x∈T,∀y∈T,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del ∧ Ready S Del :=by
  intro S hSP hreg hedit hinner hreserve
  obtain ⟨hpres,M,Del,hData⟩:=hClass S hSP hreg hedit hinner hreserve
  refine ⟨hpres,M,Del,hData,?_⟩
  exact hReady S hSP hreg hedit hinner hreserve Del hData.2.2.2.2.2.1
end Oberwolfach
