module

public import Oberwolfach.MarkedVortexConcreteChainProjections
public import Oberwolfach.MarkedVortexInnerTerminalAbsorption
public import Oberwolfach.MarkedReferenceTerminalRepresentation

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
theorem marked_vortex_concrete_terminal_representation_absorbed
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

:
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
  let levels:=markedFiniteLevels hc R
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  let chain:=markedFiniteReferenceChainToChain hc R C
  let H:=fun b v u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b v u
  let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
  let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true
  let Rglobal:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
  ∀ (i:ℕ) (T:Finset (Finset (levels 0).VP⊕((levels 0).VP×(levels 0).UP))),
    MarkedReferenceTerminalRepresentation (levels i) (chain.intoV i).toEmbedding (chain.intoU i) T →
  ∀ Reserve:Finset (Finset V⊕(V×U)),
    MarkedFixedTerminalAbsorber G π d (r+4) z.1 H Reserve
      (Q.extendedVertices ((markedReferenceClip hc i).val+1)) (Q.extendedIndices ((markedReferenceClip hc i).val+1))→
    HasResourceDecomposition Rglobal (Reserve∪T.image
      (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0)))
:= by
  intro hc R C levels chain H E K Rglobal i T hRep Reserve habs
  letI : ∀ j,Fintype (R j).VP:=fun j=>(R j).inst7
  letI : ∀ j,Fintype (R j).UP:=fun j=>(R j).inst8
  letI : ∀ j,LinearOrder (R j).VP:=fun j=>(R j).inst9
  letI : ∀ j,DecidableEq (R j).UP:=fun j=>(R j).inst10
  letI : ∀ j,Fintype (levels j).VP:=fun j=>(levels j).inst7
  letI : ∀ j,Fintype (levels j).UP:=fun j=>(levels j).inst8
  letI : ∀ j,LinearOrder (levels j).VP:=fun j=>(levels j).inst9
  letI : ∀ j,DecidableEq (levels j).UP:=fun j=>(levels j).inst10
  unfold MarkedReferenceTerminalRepresentation at hRep
  dsimp only at hRep
  obtain ⟨A,S,hS,hA,hSZ,hdiv,hT⟩:=hRep
  have hSp:∀ v∈S,v.1∈(levels i).I ∧ v.2∈(levels i).J ∧
      ((levels i).HBase false v.1 v.2∨(levels i).HBase true v.1 v.2):=by
    intro v hv
    exact ⟨(hSZ v hv).1,(hSZ v hv).2,(Finset.mem_filter.mp (hS hv)).2⟩
  have hAbs:=marked_vortex_inner_terminal_remainder_absorbed Q (markedReferenceClip hc i).val π hpres d (r+4) z.1 H A S hA hSp (by
    convert hdiv using 1 <;> congr 5 <;> first | rfl | exact Subsingleton.elim _ _) Reserve habs
  have hdeq:(fun (x y:markedVortexVertexType Q 0)=>Classical.propDecidable (x=y))=
      (fun x y=>Subtype.instDecidableEq x y):=by apply Subsingleton.elim
  letI : DecidableEq (markedVortexVertexType Q 0):=fun x y=>Classical.propDecidable (x=y)
  have hMap:T.image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0)) =
      (markedFiniteResources (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2)
        (levels i).πP A S).image (markedResourceEmbedding (markedVortexVertexEmbedding Q (markedReferenceClip hc i).val).toEmbedding
        (markedVortexHubEmbedding Q (markedReferenceClip hc i).val)):=by
    rw [hT,Finset.image_image]
    apply Finset.image_congr
    intro w hw
    have hh:=marked_vortex_ambient_resource_composition Q 0 (markedReferenceClip hc i).val (by omega) w
    try rw [← hdeq] at hh
    exact hh
  rw [hMap]
  convert hAbs using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
