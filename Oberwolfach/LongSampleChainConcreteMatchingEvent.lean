module

public import Oberwolfach.LongSampleChainReserveEvents
public import Oberwolfach.LongEveryReserveConcreteClassEvent

@[expose] public section
/-! The same sampled chain, correction and absorber reserve before and after
attaching matching and prepared-class witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

def LongSampleChainConcreteMatchingEvent
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (Bpart:ℕ) (gammaLoss sigmaLoss ξClass Δ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Chain:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))→
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop):Prop :=
  let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
  let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
    (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
  ∃D₀:MarkedReferenceDeletion P π d σ,
    D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss*n) (sigmaLoss*n) ∧
  let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
  let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
  let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
  ∃C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
    C.edges.card≤Bpart ∧ Disjoint D₀.removed C.edges ∧ Chain z D₀ C.edges ∧
    LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
      K θ Dv a γ eps βList F hF weight w D₀ C.edges ∧
    LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
      lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C.edges ∧
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C.edges≤S ∧
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Q.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C.edges S M Del

theorem long_sample_chain_matching_with_concrete_class
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (Bpart:ℕ) (gammaLoss sigmaLoss ξClass Δ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Chain:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))→
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop)
    (hConcrete:LongEveryReserveConcreteClassEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
      θ Dv a γ eps βList F hF weight w)
    (hChain:LongSampleChainMatchingEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
      θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w Chain):
    LongSampleChainConcreteMatchingEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
      θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w Chain :=by
  obtain ⟨D₀,hvalid,C,hcard,hdis,hChain,hmatch,hready⟩:=hChain
  exact ⟨D₀,hvalid,C,hcard,hdis,hChain,hmatch,hready,hConcrete D₀ hvalid C hcard hdis⟩
end Oberwolfach
