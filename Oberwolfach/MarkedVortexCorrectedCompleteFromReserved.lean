module

public import Oberwolfach.MarkedVortexActualCorrectedIteration
public import Oberwolfach.MarkedVortexCorrectedReserveInitialState
public import Oberwolfach.MarkedFiniteResourcesToDecompositionTarget
public import Oberwolfach.MarkedReferenceFiniteIteration
public import Oberwolfach.MarkedCorrectedReserveSupport
public import Oberwolfach.MarkedCorrectionAbsorberOriginal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 100000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_corrected_complete_from_reserved
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (htypes:∀v u,¬(Hglobal false v u∧Hglobal true v u))
    (hsep:∀u v w,Hglobal false v u→Hglobal true w u→v≠π w)
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
    (hRec:MarkedVortexCorrectedRecordConsequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut)

    (gammaLoss sigmaLoss:ℝ):
  let hc:0<L+1:=by omega
  let R:=fun i:Fin (L+1)=>marked_vortex_corrected_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal htypes hsep
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec i.val (by omega)
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  let C:=markedVortexCorrectedReferenceChain r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal htypes hsep
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec;
  (∀ i:Fin (L+1),MarkedReferenceLevelStepProperty (R i) gammaLoss sigmaLoss) →
  let levels:=markedFiniteLevels hc R
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  let chain:=markedFiniteReferenceChainToChain hc R C
  let H:=Hglobal
  let E:=MarkedSampleArc G π (3*d) (fun e=>σglobal (Sum.inl e)) false
  let K:=MarkedSampleArc G π (3*d) (fun e=>σglobal (Sum.inl e)) true
  let Rglobal:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
  ∀ (sizeAbs aAbs bAbs eAbs fAbs:ℕ) (εabs:ℝ),
  let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
  let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S;
  MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4)→
  MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) r sizeAbs aAbs bAbs eAbs fAbs εabs→
  (Q.extendedVertices (L+1)).card+(Q.extendedIndices (L+1)).card≤sizeAbs→
  ((Q.extendedVertices 1).card:ℝ)≤εabs*Fintype.card V+fAbs→
  ((Q.extendedIndices 1).card:ℝ)≤εabs*Fintype.card V+fAbs→
  (eAbs:ℝ)≤gammaLoss*Fintype.card (levels 0).VP→
  (eAbs:ℝ)≤sigmaLoss*Fintype.card (levels 0).VP→
  HasResourceDecomposition Rglobal (markedDecompositionTarget
    (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π) (H false) (H true)) :=by
  intro hc R C hsteps levels chain H E K Rglobal sizeAbs aAbs bAbs eAbs fAbs εabs S Full hdiv habs hsize hV hU hg hs
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  obtain ⟨Cabs,hC,hCr,hCu,havoid,hfixed,T,hT,hremain⟩:=
    marked_vortex_corrected_reserve_initial_state Q π hpres d r sizeAbs aAbs bAbs eAbs fAbs L εabs
      (gammaLoss*Fintype.card (levels 0).VP) (sigmaLoss*Fintype.card (levels 0).VP) σglobal Hglobal htypes
      hdiv habs hsize hV hU hg hs
  let Dempty:MarkedReferenceDeletion G π d σglobal:=⟨∅,∅⟩
  have hEmpty:Dempty.removed=∅:=by simp [Dempty,MarkedReferenceDeletion.removed,markedFiniteResources]
  have hfull:Dempty.remaining H=Full:=by simp [MarkedReferenceDeletion.remaining,hEmpty,Full,S] <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hprotected:Dempty.removed.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅:=by simp [hEmpty]
  have hremain':(T.remaining (levels 0).HBase).image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding
      (markedVortexHubEmbedding Q 0))=Dempty.remaining H\Cabs.edges:=by
    rw [hfull]
    convert hremain using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  have hgV:markedSampleArcSetGraph G π d σglobal Dempty.arcs=(⊥:SimpleGraph V):=by
    ext x y; simp [Dempty,markedSampleArcSetGraph,physicalEdgeGraph]
  have hgVU:markedFiniteSpokeGraph Dempty.spokes=(⊥:SimpleGraph (V⊕U)):=by
    ext x y; simp [Dempty,markedFiniteSpokeGraph,physicalEdgeGraph]
  have hfixed':MarkedFixedTerminalAbsorber G π d (r+4)
      (rawMarkedDeleteRims σglobal (markedSampleArcSetGraph G π d σglobal Dempty.arcs).edgeFinset)
      (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph Dempty.spokes)) Cabs.edges
      (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)):=by
    rw [hgV,graph_bottom_edgeFinset_any_instance _,rawMarkedDeleteRims_empty,hgVU,markedDeletePhysicalSpokes_bottom]
    exact hfixed
  have hT':T.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
      (gammaLoss*Fintype.card (levels 0).VP) (sigmaLoss*Fintype.card (levels 0).VP):=by
    convert hT using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  have hdec:=marked_vortex_actual_corrected_iteration r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal htypes hsep
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec
    gammaLoss sigmaLoss hsteps T hT' Dempty Cabs.edges hremain' hprotected hfixed'
  rw [hfull] at hdec
  dsimp only [Full,S] at hdec
  rw [marked_finite_resources_univ_eq_decomposition_target] at hdec
  exact hdec
end Oberwolfach
