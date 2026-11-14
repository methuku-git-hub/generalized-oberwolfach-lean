module

public import Oberwolfach.LongFirstVortexProtectionGraph
public import Oberwolfach.LongSelectorReserveGraphBounded
public import Oberwolfach.LongProtectedRegularClassSelection
public import Oberwolfach.LongEveryClassSameDeletionReady

@[expose] public section
/-! Uniformly select an actual class and matching for any bounded protected
reserve, including the reserve selected later by a level-chain construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 35000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_every_reserve_concrete_class_matching
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hε:0≤ε) (αHost:ℝ) (hsmall:ε≤αHost/100000)
    (B:ℕ) (gammaLoss sigmaLoss ξClass Δ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ Dmatch a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hEvery:LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z
      (Q.extendedVertices 1) (Q.extendedIndices 1) K B θ Dmatch a γ eps βList F hF weight w)
    (hPart:∀T:SimpleGraph (Fin n),(∀v,T.degree v≤B)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,(spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)⊔T).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n))
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (hvalid:D₀.Valid
      (retainedRawMarkedSpokes π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) z.2 false false)
      (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss*n) (sigmaLoss*n))
    (C:MarkedSupportedEdgeSet
      (fun x:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims (fun e=>rawExpandedMarkedCollapse e (z.1 e))
        (markedSampleArcSetGraph P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)) D₀.arcs).edgeFinset (Sum.inl e)) false=>x.val.1)
      (fun x=>x.val.2)
      (fun x:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims (fun e=>rawExpandedMarkedCollapse e (z.1 e))
        (markedSampleArcSetGraph P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)) D₀.arcs).edgeFinset (Sum.inl e)) true=>x.val.1)
      (fun x=>x.val.2) π U)
    (hcard:C.edges.card≤B) (hdis:Disjoint D₀.removed C.edges):
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C.edges≤S ∧
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Q.extendedVertices 1) K θ Dmatch a γ eps βList F hF weight w D₀ C.edges S M Del :=by
  have hInner:∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,x≠y→
      (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)).Adj x y:=
    (long_first_vortex_protection_graph P Dv mm β ε αHost Q hε hsmall).2
  obtain ⟨A,hAeq,hAsample,hAcard,hmatch⟩:=long_selector_bounded_reserve_graph_before_class Δ P π d r
    gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1) (Q.extendedIndices 1) K B θ Dmatch a γ eps βList
    F hF weight w hEvery D₀ hvalid C hcard hdis
  have hAdeg:∀v,(markedResourceRimGraph C.edges).degree v≤B:=by
    intro v
    rw [←hAeq]
    exact (A.degree_le_card_edgeFinset v).trans hAcard
  have hSample:markedResourceRimGraph C.edges≤longPhysicalStateGraph P z.1 {0,1,2,3,4}:=by
    simpa only [hAeq] using hAsample
  obtain ⟨S,hSP,hregS,hedit,hinner,hreserve⟩:=long_protected_regular_class_selection P
    (longPhysicalStateGraph P z.1 {0,1,2,3,4}) (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1))
    (markedResourceRimGraph C.edges) (Q.extendedVertices 1) (Fintype.card U) B ξClass hInner hAdeg hSample hPart
  obtain ⟨hselected,M,Del,hData,_⟩:=long_every_class_same_deletion_ready Δ P π d r gammaLoss sigmaLoss ξClass z
    (Q.extendedVertices 1) K θ Dmatch a γ eps βList F hF weight w D₀ C.edges hmatch (fun _ _=>True)
    (by intro S hSP hreg hedit hinner hreserve Del hDel;trivial) S hSP hregS hedit hinner hreserve
  exact ⟨S,hSP,hregS,hedit,hinner,hreserve,hselected,M,Del,hData⟩
end Oberwolfach
