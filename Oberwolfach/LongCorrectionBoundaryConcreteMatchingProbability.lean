module

public import Oberwolfach.LongCorrectionUniversalMatchingReserve
public import Oberwolfach.LongEveryReserveConcreteClassEvent
public import Oberwolfach.FirstVortexConcreteBoundaryEvent

@[expose] public section
/-! Preserve any common-event probability while selecting the correction,
terminal absorber and universal matching witnesses on that same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 45000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_correction_boundary_concrete_matching_probability
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length) (hreg:P.IsRegularOfDegree Dv) (hn:0<n) (hD:0<Dv)
    (hρhi:initialIndexDensity U Dv≤1) (hε:0≤ε)
    (size a₀ b₀ e₀ f₀ Bpart:ℕ) (εAbs ζCorr ξCorr gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (heAbs:ε≤εAbs) (hsize:2*mm≤size) (hξ:0≤ξCorr)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n))
    (hExtra:(e₀:ℝ)≤extra*n) (hB:e₀≤Bpart)
    (θ a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (ρ₀ BM:ℝ) (BO:Fin K→ℝ) (ξSeed ΔSeed ζret ζselect terr τerr:ℝ)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U))) (hF₀:F₀.card≤f₀)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Prior:MarkedExpandedActualOutcome (U:=U) π d→Prop) (bProb:ℝ):
    bProb≤μ.probability (fun z=>
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ((Prior z ∧ FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)) ∧
    LongEveryReserveConcreteClassEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
      θ Dv a γ eps βList F hF weight w) ∧
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H
      (Q.extendedVertices 1) (Q.extendedIndices 1) ∧
    LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1) (Q.extendedIndices 1)
      K Bpart θ Dv a γ eps βList F hF weight w
    )→
    bProb≤μ.probability (fun z=>
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ((Prior z ∧ FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)) ∧
    LongEveryReserveConcreteClassEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
      θ Dv a γ eps βList F hF weight w) ∧
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
      D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧ Disjoint D₀.removed C.edges    ) :=by
  intro hb
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨D₀,hvalid,havoid,C,hF,hCe,hCr,hCu,hfixed,horiginal,hmatch,D₂,hvalid₂,hremoved,hremain,hdis⟩:=
    long_correction_universal_matching_reserve P π d r Dv mm β ε Q hpres L hL hreg hn hD hρhi hε
      size a₀ b₀ e₀ f₀ Bpart εAbs ζCorr ξCorr gammaLoss sigmaLoss extra ξClass Δ heAbs hsize hξ hbudget hExtra hB
      z θ a γ eps βList F hF weight w F₀ hF₀ hz.2.1 hz.2.2
  have hconcrete:=hz.1.2 D₀ hvalid C (hCe.trans hB) hdis
  exact ⟨hz.1,D₀,hvalid,havoid,C,hF,hCe,hCr,hCu,hfixed,horiginal,hmatch,hconcrete,D₂,hvalid₂,hremoved,hremain,hdis⟩
end Oberwolfach
