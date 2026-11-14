module

public import Oberwolfach.LongFirstVortexProtectionGraph
public import Oberwolfach.LongSelectorReserveGraphBounded
public import Oberwolfach.LongProtectedRegularClassSelection
public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.MarkedProtectedCorrectionVortexReserve
public import Oberwolfach.LongEveryClassValidDeletionEvent
public import Oberwolfach.MarkedActualSampleMatchingDisjoint

@[expose] public section
/-! Select the actual correction and terminal reserve first, then retain the
universal long matching witness on the same expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 35000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_correction_reserve_concrete_class_matching
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length) (hreg:P.IsRegularOfDegree Dv) (hn:0<n) (hD:0<Dv)
    (hρhi:initialIndexDensity U Dv≤1) (hε:0≤ε)
    (αHost:ℝ) (hsmall:ε≤αHost/100000)
    (size a₀ b₀ e₀ f₀ Bpart:ℕ) (εAbs ζCorr ξCorr gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (heAbs:ε≤εAbs) (hsize:2*mm≤size) (hξ:0≤ξCorr)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n))
    (hExtra:(e₀:ℝ)≤extra*n) (hB:e₀≤Bpart)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U))) (hF₀:F₀.card≤f₀):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H
      (Q.extendedVertices 1) (Q.extendedIndices 1)→
    LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1) (Q.extendedIndices 1)
      K Bpart θ Dv a γ eps βList F hF weight w→
    (∀T:SimpleGraph (Fin n),(∀v,T.degree v≤Bpart)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,(spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)⊔T).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n))→
    ∃D₀:MarkedReferenceDeletion P π d σ,
      D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss*n) (sigmaLoss*n) ∧
      MarkedDeletionAvoidsApproximateMatching P π d z D₀ ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
    let E':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) false
    let K':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) true;
    ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2) (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      MarkedFixedTerminalAbsorber P π d (r+4) σ' H' C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
      MarkedFixedTerminalAbsorber P π d (r+4) σ H C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C.edges ∧
      (∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
        (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
        markedResourceRimGraph C.edges≤S ∧
        (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
        ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
          LongClassMatchingDeletionWitness Δ P π d r z (Q.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C.edges S M Del) ∧
    ∃D₂:MarkedReferenceDeletion P π d σ,
      D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) ((gammaLoss+extra)*n) ((sigmaLoss+extra)*n) ∧
      D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧ Disjoint D₀.removed C.edges :=by
  intro σ H hCorr hEvery hPart
  have hsep:∀v u,¬(H false v u∧H true v u):=by
    intro v u
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false v u
  have hb:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*Fintype.card (Fin n))≤min (gammaLoss*n) (sigmaLoss*n):=by
    simpa only [Fintype.card_fin] using hbudget
  obtain ⟨D₀,hvalid,C,havoidF,hCe,hCr,hCu,hfixed,horiginal,D₂,hvalid₂,hremoved,hremain,hdis⟩:=
    marked_protected_correction_vortex_reserve r d size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr P Dv mm β ε Q π hpres L hL σ H
      hreg (by simpa using hn) hD hρhi hε heAbs hsize (gammaLoss*n) (sigmaLoss*n) (extra*n) hξ hb hsep hCorr F₀ hF₀ hExtra
  have hmatch:=hEvery D₀ hvalid C (hCe.trans hB) hdis
  have havoid:=marked_actual_sample_deletion_avoids_matching P π d z D₀ hvalid.1
  have hInner:∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,x≠y→
      (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)).Adj x y:=
    (long_first_vortex_protection_graph P Dv mm β ε αHost Q hε hsmall).2
  obtain ⟨A,hAeq,hAsample,hAcard,_⟩:=long_selector_bounded_reserve_graph_before_class Δ P π d r
    gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1) (Q.extendedIndices 1) K Bpart θ Dv a γ eps βList
    F hF weight w hEvery D₀ hvalid C (hCe.trans hB) hdis
  have hAdeg:∀v,(markedResourceRimGraph C.edges).degree v≤Bpart:=by
    intro v
    rw [←hAeq]
    exact (A.degree_le_card_edgeFinset v).trans hAcard
  have hSample:markedResourceRimGraph C.edges≤longPhysicalStateGraph P z.1 {0,1,2,3,4}:=by
    simpa only [hAeq] using hAsample
  obtain ⟨S,hSP,hregS,hedit,hinner,hreserve⟩:=long_protected_regular_class_selection P
    (longPhysicalStateGraph P z.1 {0,1,2,3,4}) (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1))
    (markedResourceRimGraph C.edges) (Q.extendedVertices 1) (Fintype.card U) Bpart ξClass hInner hAdeg hSample hPart
  obtain ⟨hselected,M,Del,hData,_⟩:=long_every_class_same_deletion_ready Δ P π d r gammaLoss sigmaLoss ξClass z
    (Q.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C.edges hmatch (fun _ _=>True)
    (by intro S hSP hreg hedit hinner hreserve Del hDel;trivial) S hSP hregS hedit hinner hreserve
  refine ⟨D₀,hvalid,havoid,C,havoidF,hCe,hCr,hCu,hfixed,horiginal,hmatch,
    ⟨S,hSP,hregS,hedit,hinner,hreserve,hselected,M,Del,hData⟩,D₂,?_,hremoved,hremain,hdis⟩
  simpa only [add_mul] using hvalid₂
end Oberwolfach
