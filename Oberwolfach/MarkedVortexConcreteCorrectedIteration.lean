module

public import Oberwolfach.MarkedVortexConcreteTerminalAbsorption
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
theorem marked_vortex_concrete_corrected_iteration
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
  let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
  let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true
  let Rglobal:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
  ∀ (T₀:MarkedReferenceDeletion (levels 0).PP (levels 0).πP d (levels 0).σBase),
    T₀.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
      (gammaLoss*Fintype.card (levels 0).VP) (sigmaLoss*Fintype.card (levels 0).VP)→
  ∀ (D₀:MarkedReferenceDeletion G π d z.1) (Reserve:Finset (Finset V⊕(V×U))),
    (T₀.remaining (levels 0).HBase).image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding
      (markedVortexHubEmbedding Q 0))=D₀.remaining H\Reserve→
    D₀.removed.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅→
    MarkedFixedTerminalAbsorber G π d (r+4)
      (rawMarkedDeleteRims z.1 (markedSampleArcSetGraph G π d z.1 D₀.arcs).edgeFinset)
      (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)) Reserve
      (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1))→
    HasResourceDecomposition Rglobal (D₀.remaining H)
:= by
  intro hc R C hsteps levels chain H E K Rglobal T₀ hT₀ D₀ Reserve hremain hprotected habs
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  letI : DecidableEq (markedVortexVertexType Q 0):=fun x y=>Classical.propDecidable (x=y)
  let F0:=markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0)
  let Ffirst:=markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0)
  let B0:Finset (Finset (levels 0).VP⊕((levels 0).VP×(levels 0).UP)):=
    (T₀.remaining (levels 0).HBase).image Ffirst
  have hFid:(Ffirst:Finset (levels 0).VP⊕((levels 0).VP×(levels 0).UP) → _)=id:=by
    funext w
    cases w with
    | inl A=>
      simp only [Ffirst,markedResourceEmbedding,Function.Embedding.sumMap,Function.Embedding.coeFn_mk,Sum.map_inl]
      congr 1
      ext v
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x,hx,hxv⟩
        change chain.intoV 0 x=v at hxv
        rw [chain.firstV] at hxv
        exact hxv ▸ hx
      · intro hv
        exact ⟨v,hv,chain.firstV v⟩
    | inr x=>
      cases x with
      | mk v u=>
        change Sum.inr ((chain.intoV 0) v,(chain.intoU 0) u)=Sum.inr (v,u)
        rw [chain.firstV,chain.firstU]
  have hB:B0.image F0=D₀.remaining H\Reserve:=by
    dsimp only [B0]
    rw [hFid,Finset.image_id]
    exact hremain
  have hsub:=marked_corrected_reserve_subset_remaining G π d (r+4) z.1 H D₀ Reserve
    (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) habs
  have horiginal:=marked_correction_absorber_fixed_original G π d (r+4) z.1 H D₀ Reserve
    (Q.extendedVertices 1) (Q.extendedVertices (L+1)) (Q.extendedIndices 1) (Q.extendedIndices (L+1))
    (hpres 1) (Q.extendedVertices_subset (by omega)) (Q.extendedIndices_subset (by omega)) hprotected habs
  have hs:∀ i,i<L+1→MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss:=by
    intro i hi;exact hsteps (markedReferenceClip hc i)
  obtain ⟨T,hTsub,hdec,hinner,hrep⟩:=marked_reference_finite_iteration levels (L+1) hc gammaLoss sigmaLoss chain hs T₀ hT₀
  have hrep':MarkedReferenceTerminalRepresentation (levels L) (chain.intoV L).toEmbedding (chain.intoU L) T:=by
    have heqL:L+1-1=L:=by omega
    change MarkedReferenceTerminalRepresentation (levels (L+1-1))
      (chain.intoV (L+1-1)).toEmbedding (chain.intoU (L+1-1)) T at hrep
    rw [heqL] at hrep
    convert hrep using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  have habs':MarkedFixedTerminalAbsorber G π d (r+4) z.1 H Reserve
      (Q.extendedVertices ((markedReferenceClip hc L).val+1)) (Q.extendedIndices ((markedReferenceClip hc L).val+1)):=by
    simpa only [markedReferenceClip,Nat.add_sub_cancel_right,Nat.min_self] using horiginal
  have hterminal:=marked_vortex_concrete_terminal_representation_absorbed r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec L T hrep' Reserve habs'
  have hdecGlobal:HasResourceDecomposition Rglobal ((B0\T).image F0):=by
    apply marked_vortex_ambient_decomposition_lift Q 0 π hpres d (r+4) z.1 H _
    convert hdec using 1 <;> congr 5 <;> first | rfl | (funext W; congr 4 <;> first | rfl | exact Subsingleton.elim _ _) | exact Subsingleton.elim _ _
  have hLsub:T.image F0⊆B0.image F0:=Finset.image_subset_image hTsub
  have hRdis:Disjoint Reserve (B0.image F0):=by rw [hB];exact Finset.disjoint_left.mpr (fun _ ha hb=>(Finset.mem_sdiff.mp hb).2 ha)
  have hdis:Disjoint ((B0\T).image F0) (Reserve∪T.image F0):=by
    rw [Finset.image_sdiff _ _ F0.injective]
    apply Finset.disjoint_union_right.mpr
    exact ⟨hRdis.symm.mono_left Finset.sdiff_subset,
      Finset.disjoint_left.mpr (fun _ ha hb=>(Finset.mem_sdiff.mp ha).2 hb)⟩
  have hwhole:=resource_decomposition_union Rglobal _ _ hdecGlobal hterminal hdis
  have heq:(B0\T).image F0∪(Reserve∪T.image F0)=D₀.remaining H:=by
    rw [Finset.image_sdiff _ _ F0.injective,hB]
    ext w
    have h₁:=fun hw=>hsub (x:=w) hw
    have h₂:=fun hw=>hLsub (x:=w) hw
    rw [hB] at h₂
    simp only [Finset.mem_sdiff] at h₂
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rwa [heq] at hwhole
end Oberwolfach
