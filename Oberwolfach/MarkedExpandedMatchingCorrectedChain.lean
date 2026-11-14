module

public import Oberwolfach.MarkedParentMatchingCorrectedChain

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
theorem marked_expanded_matching_corrected_chain
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
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
    (hβA:βA≤βCommon) (hζκ:ζCommon≤κ/4)
    (hC:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (hP:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
    (hrec:βrec≤βA) (herr:tolRef+(r+12:ℕ)*ζActive≤κ/4) (hζActiveK:ζActive≤κ/4)
    (hεeq:εref=κ/4) (hδeq:δref=κ)
    (hpot:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤κ/4)
    (hdeep:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤thetaDeep/4)
    (hx:0≤x) (hbal:epsBal+((r+4)+2:ℕ)*ζBal≤etaBal)
    (hmargin:epsBal+((r+4)+2:ℕ)*ζBal≤x/2) (hterminal:L+1=Q.length)
    (hrowmargin:rowErr+ζRow≤(s₀/((r+4:ℕ):ℝ))/8)
    (hloadmargin:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide≤eta/4)
    (hbquarter:β≤1/4) (hh:0≤hIcut) (hδα:deltaI≤(α/2)/32) (hδstar:deltaI≤kstar/32)
    (hδt:2*deltaI≤tstar/8) (hhstar:2*hIcut≤(α/2)*kstar/4) (hhs:2*hIcut≤tstar/8-ζCut)
    (hEndpoint:tolRef+(r+12:ℕ)*ζActive≤x/2)
    (sizeCorr aCorr bCorr eCorr fCorr:ℕ) (gammaLoss sigmaLoss ξCorr εCorr ζCorr:ℝ) (hξCorr:0≤ξCorr)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*Fintype.card V)≤
      min (gammaLoss*Fintype.card V) (sigmaLoss*Fintype.card V))
    (Ω:Type) (mass:Ω→ℝ) (selected:Ω→RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (Other:Ω→Prop)
    (hCorrect:∀ outcome,Other outcome → MarkedProtectedAbsorbableCorrectionWithBounds G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr (selected outcome).1
      (retainedRawMarkedSpokes π d (fun e=>(selected outcome).1 (Sum.inr e)) a (startRetentionMinimum (rawStartHubSet π d (fun e=>(selected outcome).1 (Sum.inr e)) a)) (selected outcome).2 a j)
      (Q.extendedVertices 1) (Q.extendedIndices 1))
    (hSelect:∃ outcome,0<mass outcome ∧ Other outcome ∧ MarkedVortexParentRecordEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight (selected outcome)):
    ∃ outcome,0<mass outcome ∧ Other outcome ∧ ∃ hGood:MarkedVortexParentRecordEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight (selected outcome),
  let hRec:=marked_vortex_parent_record_event_consequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight (selected outcome) hGood βA βrec κ thetaDeep etaBal x eta deltaI hIcut
    hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hx hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint

  (let hc:0<L+1:=by omega
  let R:=fun i:Fin (L+1)=>marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight (selected outcome)
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec i.val (by omega)
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  Nonempty (MarkedFiniteReferenceChain hc R)) ∧
  (let H:=retainedRawMarkedSpokes π d (fun e=>(selected outcome).1 (Sum.inr e)) a (startRetentionMinimum (rawStartHubSet π d (fun e=>(selected outcome).1 (Sum.inr e)) a)) (selected outcome).2 a j
  let E:=MarkedSampleArc G π (3*d) (fun e=>(selected outcome).1 (Sum.inl e)) false
  let K:=MarkedSampleArc G π (3*d) (fun e=>(selected outcome).1 (Sum.inl e)) true
  let R:=marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight (selected outcome)
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec 0 (by omega)
  letI : Fintype R.VP:=R.inst7
  letI : Fintype R.UP:=R.inst8
  letI : LinearOrder R.VP:=R.inst9
  letI : DecidableEq R.UP:=R.inst10
∃ (DA:Finset (E⊕K)) (DS:Finset (V×U)) (D₀:MarkedReferenceDeletion G π d (selected outcome).1),
    D₀.arcs=DA ∧ D₀.spokes=DS ∧
  ∃ T:MarkedReferenceDeletion R.PP R.πP d R.σBase,
    T.Valid R.HBase (r+4) R.I R.J (gammaLoss*Fintype.card R.VP) (sigmaLoss*Fintype.card R.VP) ∧
    T.removed.image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₀.removed ∧
    (T.remaining R.HBase).image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₀.remaining H ∧
    let σ':=rawMarkedDeleteRims (selected outcome).1 (markedSampleArcSetGraph G π d (selected outcome).1 DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r sizeCorr aCorr bCorr eCorr fCorr εCorr) := by
  obtain ⟨outcome,hMass,hOther,hGood⟩:=hSelect
  have hCorr:=hCorrect outcome hOther
  refine ⟨outcome,hMass,hOther,hGood,?_⟩
  let z:=selected outcome
  let hRec:=marked_vortex_parent_record_event_consequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z hGood βA βrec κ thetaDeep etaBal x eta deltaI hIcut
    hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hx hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint

  constructor
  · exact marked_vortex_parent_event_reference_chain r k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
      βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hx hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint
  · exact (marked_vortex_bounded_correction_initial_state r k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
      βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec
      sizeCorr aCorr bCorr eCorr fCorr gammaLoss sigmaLoss ξCorr εCorr ζCorr hξCorr hbudget) hCorr
end Oberwolfach
