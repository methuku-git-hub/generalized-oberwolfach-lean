module

public import Oberwolfach.MarkedActualCorrectionReserveMatching
public import Oberwolfach.MarkedCorrectionAbsorberOriginal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_actual_correction_reserve_original_matching
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Bool→ℝ) (s:U→Bool→ℝ)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (outcome:MarkedExpandedActualOutcome (U:=U) π d)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ) (N NI Kgeom:ℕ)
    (hd:1≤d) (he:0≤ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u false=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u false=s₀)
    (hXi0:0≤xiDeep) (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep≤κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep≤(s₀/(((r+4):ℕ):ℝ))*ω/32)
    (hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i))
    (hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i))
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (hRec:MarkedVortexParentRecordConsequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome) βA βrec κ thetaDeep etaBal x eta deltaI hIcut)
    (sizeCorr aCorr bCorr eCorr fCorr:ℕ) (εCorr gamma₀ sigma₀ extra:ℝ)
    (D₀:MarkedReferenceDeletion G π d (markedExpandedActualSelected π d outcome).1):
  let H:=retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false
  let σ':=rawMarkedDeleteRims (markedExpandedActualSelected π d outcome).1 (markedSampleArcSetGraph G π d (markedExpandedActualSelected π d outcome).1 D₀.arcs).edgeFinset
  let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
  let E':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false
  let K':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true
  let R:=marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome)
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec 0 (by omega)
  letI : Fintype R.VP:=R.inst7
  letI : Fintype R.UP:=R.inst8
  letI : LinearOrder R.VP:=R.inst9
  letI : DecidableEq R.UP:=R.inst10
  D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
    (gamma₀*Fintype.card V) (sigma₀*Fintype.card V) →
  (∀v u,¬(H false v u∧H true v u)) →
  MarkedReservedTerminalAbsorberProperty (fun x:E'=>x.val.1) (fun x=>x.val.2)
    (fun x:K'=>x.val.1) (fun x=>x.val.2) (H' false) (H' true) π (3*d) r sizeCorr aCorr bCorr eCorr fCorr εCorr →
  ∀ (X W:Finset V) (Z B:Finset U),
    X.card+Z.card≤sizeCorr → X⊆W → Z⊆B → Q.extendedVertices 1⊆W → Q.extendedIndices 1⊆B →
    (W.card:ℝ)≤εCorr*Fintype.card V+fCorr → (B.card:ℝ)≤εCorr*Fintype.card V+fCorr →
  ∀ F₀:Finset (Finset V⊕(V×U)), F₀.card≤fCorr → (eCorr:ℝ)≤extra*Fintype.card V →
  ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2)
      (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
    Disjoint C.edges F₀ ∧ C.edges.card≤eCorr ∧ C.rows.card≤aCorr ∧ C.hubs.card≤bCorr ∧
    MarkedFixedTerminalAbsorber G π d (r+4) σ' H' C.edges X Z ∧
    (X⊆Q.extendedVertices 1 → Z⊆Q.extendedIndices 1 →
      MarkedFixedTerminalAbsorber G π d (r+4) (markedExpandedActualSelected π d outcome).1 H C.edges X Z) ∧
  ∃ D₂:MarkedReferenceDeletion G π d (markedExpandedActualSelected π d outcome).1,
    D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
      ((gamma₀+extra)*Fintype.card V) ((sigma₀+extra)*Fintype.card V) ∧
    MarkedDeletionAvoidsApproximateMatching G π d outcome D₂ ∧
    D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧ Disjoint D₀.removed C.edges ∧
  ∃ T:MarkedReferenceDeletion R.PP R.πP d R.σBase,
    T.Valid R.HBase (r+4) R.I R.J ((gamma₀+extra)*Fintype.card R.VP) ((sigma₀+extra)*Fintype.card R.VP) ∧
    T.removed.image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₂.removed ∧
    (T.remaining R.HBase).image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₂.remaining H := by
  intro H σ' H' E' K' R hvalid hsep hprop X W Z B hsize hX hZ hI hJ hW hB F₀ hF heCorr
  letI : Fintype R.VP:=R.inst7
  letI : Fintype R.UP:=R.inst8
  letI : LinearOrder R.VP:=R.inst9
  letI : DecidableEq R.UP:=R.inst10
  obtain ⟨C,hF₀,hCe,hCr,hCu,hfixed,D₂,h₂,havoid,hremoved,hremain,hdis,T,hT,hTremoved,hTremain⟩:=
    marked_actual_correction_reserve_matching r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s weightParent weight outcome
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec
    sizeCorr aCorr bCorr eCorr fCorr εCorr gamma₀ sigma₀ extra D₀ hvalid hsep hprop X W Z B hsize hX hZ hI hJ hW hB F₀ hF heCorr
  refine ⟨C,hF₀,hCe,hCr,hCu,hfixed,?_,D₂,h₂,havoid,hremoved,hremain,hdis,T,hT,hTremoved,hTremain⟩
  intro hXI hZJ
  exact marked_correction_absorber_fixed_original G π d (r+4) (markedExpandedActualSelected π d outcome).1 H D₀ C.edges
    (Q.extendedVertices 1) X (Q.extendedIndices 1) Z (hpres 1) hXI hZJ hvalid.2.1 hfixed
end Oberwolfach
