module

public import Oberwolfach.MarkedVortexRecordInitialState
public import Oberwolfach.MarkedCorrectionSelectReserve

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_select_correction_reserve
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ) (N NI Kgeom:ℕ)
    (hd:1≤d) (he:0≤ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u a=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u j=s₀)
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
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z βA βrec κ thetaDeep etaBal x eta deltaI hIcut)
    (sizeCorr aCorr bCorr eCorr fCorr:ℕ) (εCorr gamma₀ sigma₀ extra:ℝ)
    (D₀:MarkedReferenceDeletion G π d z.1):
  let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
  let σ':=rawMarkedDeleteRims z.1 (markedSampleArcSetGraph G π d z.1 D₀.arcs).edgeFinset
  let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
  let E':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false
  let K':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true
  let R:=marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
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
  ∃ D₂:MarkedReferenceDeletion G π d z.1,
    D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
      ((gamma₀+extra)*Fintype.card V) ((sigma₀+extra)*Fintype.card V) ∧
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
  obtain ⟨C,hF₀,hCe,hCr,hCu,hfixed,D₂,h₂,hremoved,hremain,hdis⟩:=
    marked_correction_select_reserve G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr z.1 H
      (Q.extendedVertices 1) (Q.extendedIndices 1) (gamma₀*Fintype.card V) (sigma₀*Fintype.card V)
      (extra*Fintype.card V) D₀ hvalid hsep hprop X W Z B hsize hX hZ hI hJ (hpres 1) hW hB F₀ hF heCorr
  have h₂':D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
      ((gamma₀+extra)*Fintype.card V) ((sigma₀+extra)*Fintype.card V):=by simpa only [add_mul] using h₂
  obtain ⟨T,hT,hTremoved,hTremain⟩:=marked_vortex_record_initial_valid_state r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec (gamma₀+extra) (sigma₀+extra) D₂ h₂'
  exact ⟨C,hF₀,hCe,hCr,hCu,hfixed,D₂,h₂',hremoved,hremain,hdis,T,hT,hTremoved,hTremain⟩
end Oberwolfach
