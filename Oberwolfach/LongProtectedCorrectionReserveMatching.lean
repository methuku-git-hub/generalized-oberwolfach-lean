module

public import Oberwolfach.MarkedProtectedCorrectionVortexReserve
public import Oberwolfach.LongBinaryFirstVortexClassForSameSampleCorrection

@[expose] public section
/-! The bounded correction, the first-vortex protected class, its matching,
and the original terminal reserve are selected from one expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_protected_correction_reserve_matching
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
    (θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ a γ βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false
    let Zpart:=spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1);
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H
      (Q.extendedVertices 1) (Q.extendedIndices 1)→
    LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1) (Q.extendedIndices 1)
      K Bpart θ Dv a γ eps βList F hF weight w→
    (∀T:SimpleGraph (Fin n),(∀v,T.degree v≤Bpart)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*binaryClassMultiplicity Dv (Fintype.card U) 0) ∧
        (∀x y,(Zpart⊔T).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n))→
    (∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (S:SimpleGraph (Fin n)),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph Reserve≤S→
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P S π Dv mm d (r+4) β ε Q F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2)→
    ∃D₀:MarkedReferenceDeletion P π d σ,
      D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss*n) (sigmaLoss*n) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
    let E':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) false
    let K':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) true;
    ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2) (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
      C.edges.card≤e₀ ∧ Disjoint D₀.removed C.edges ∧
      MarkedFixedTerminalAbsorber P π d (r+4) σ H C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
    ∃(S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      LongClassMatchingDeletionWitness Δ P π d r z (Q.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C.edges S M Del ∧
      (∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P S π Dv mm d (r+4) β ε Q F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) :=by
  intro σ H Zpart hCorr hEvery hPart hPrepared
  have hsep:∀v u,¬(H false v u∧H true v u):=by
    intro v u
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false v u
  have hb:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*Fintype.card (Fin n))≤min (gammaLoss*n) (sigmaLoss*n):=by simpa only [Fintype.card_fin] using hbudget
  obtain ⟨D₀,hvalid,C,_,hCe,_,_,_,hfixed,D₂,hvalid₂,hremoved,hremain,hdis⟩:=
    marked_protected_correction_vortex_reserve r d size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr P Dv mm β ε Q π hpres L hL σ H
      hreg (by simpa using hn) hD hρhi hε heAbs hsize (gammaLoss*n) (sigmaLoss*n) (extra*n) hξ hb hsep hCorr ∅ (by simp) hExtra
  obtain ⟨S,M,Del,hw,hinner,hpacking,hedit⟩:=
    long_binary_first_vortex_class_for_same_sample_correction P π d r Dv mm β ε Q αHost hε hsmall gammaLoss sigmaLoss ξClass z
      θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList F hF weight w Bpart hEvery D₀ hvalid C (hCe.trans hB) hdis hPart (hPrepared C.edges)
  exact ⟨D₀,hvalid,C,hCe,hdis,hfixed,S,M,Del,hw,hinner,hpacking,hedit⟩
end Oberwolfach
