module

public import Oberwolfach.MarkedVortexConcreteChainProjections
public import Oberwolfach.MarkedReferenceEmbeddedStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 80000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_concrete_reference_nonterminal_step
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

    (gammaLoss sigmaLoss:ℝ):
  let hc:0<L+1:=by omega
  let R:=fun i:Fin (L+1)=>marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec i.val (by omega)
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  let C:=markedVortexConcreteReferenceChain r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec;
  (∀ i:Fin (L+1),MarkedReferenceLevelStepProperty (R i) gammaLoss sigmaLoss) →
  let levels:=markedFiniteLevels hc R
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  let chain:=markedFiniteReferenceChainToChain hc R C
  let H:=fun b v u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b v u
  let State:=fun i=>MarkedReferenceDeletion (levels i).PP (levels i).πP d (levels i).σBase
  let Good:=fun i (T:State i)=>T.Valid (levels i).HBase (r+4) (levels i).I (levels i).J
    (gammaLoss*Fintype.card (levels i).VP) (sigmaLoss*Fintype.card (levels i).VP)
  let B:=fun i (T:State i)=>(T.remaining (levels i).HBase).image
    (markedResourceEmbedding (markedVortexVertexEmbedding Q (markedReferenceClip hc i).val).toEmbedding
      (markedVortexHubEmbedding Q (markedReferenceClip hc i).val))
  let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
  let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true
  let Rglobal:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
  ∀ i<L,∀ T:State i,Good i T→∃ Tnext:State (i+1),Good (i+1) Tnext ∧
    B (i+1) Tnext⊆B i T ∧ HasResourceDecomposition Rglobal (B i T\B (i+1) Tnext)
:= by
  intro hc R C hsteps levels chain H State Good B E K Rglobal i hi T hT
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  have hdeq:(fun (x y:markedVortexVertexType Q 0)=>Classical.propDecidable (x=y))=
      (fun x y=>Subtype.instDecidableEq x y):=by apply Subsingleton.elim
  letI : DecidableEq (markedVortexVertexType Q 0):=fun x y=>Classical.propDecidable (x=y)
  let F0:=markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0)
  let B0:=fun i (T:State i)=>(T.remaining (levels i).HBase).image
    (markedResourceEmbedding (chain.intoV i).toEmbedding (chain.intoU i))
  have heq (j:ℕ) (T:State j):B j T=(B0 j T).image F0:=by
    dsimp only [B,B0]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro w hw
    change markedResourceEmbedding (markedVortexVertexEmbedding Q (markedReferenceClip hc j).val).toEmbedding
      (markedVortexHubEmbedding Q (markedReferenceClip hc j).val) w =
      F0 (markedResourceEmbedding (chain.intoV j).toEmbedding (chain.intoU j) w)
    symm
    have hh:=marked_vortex_ambient_resource_composition Q 0 (markedReferenceClip hc j).val (by omega) w
    try rw [← hdeq] at hh
    exact hh
  have hs:∀ i,i<L+1→MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss:=by
    intro k hk
    exact hsteps (markedReferenceClip hc k)
  obtain ⟨Tnext,hTnext,hsub,hdec⟩:=marked_reference_embedded_iteration_step levels (L+1) hc gammaLoss sigmaLoss chain hs i (by omega) T hT
  refine ⟨Tnext,hTnext,?_,?_⟩
  · rw [heq,heq]
    exact Finset.image_subset_image hsub
  · rw [heq,heq,←Finset.image_sdiff _ _ F0.injective]
    apply marked_vortex_ambient_decomposition_lift Q 0 π hpres d (r+4) z.1 H _
    convert hdec using 1 <;> congr 5 <;> first | rfl | (funext W; congr 4 <;> first | rfl | exact Subsingleton.elim _ _) | exact Subsingleton.elim _ _
end Oberwolfach
