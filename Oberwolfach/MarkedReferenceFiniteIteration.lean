module

public import Oberwolfach.MarkedUniformReferenceLevelStep
public import Oberwolfach.MarkedReferenceTerminalRepresentation
public import Oberwolfach.MarkedReferenceLevelEmbedding
public import Oberwolfach.MarkedResourceEmbeddingComposition
public import Oberwolfach.ReindexedResourceIteration

@[expose] public section

/-! Iteration of the constructed fixed-reference cover-down step. The
individual level estimates are explicit inputs; no packing or next-state
existence is assumed. The last remainder is retained on the last inner
pair without requiring an additional analytic level at the terminal scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_reference_finite_iteration
    (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss:ℝ):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    (∀ i,i<count → MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss) →
    ∀ D₀:MarkedReferenceDeletion (levels 0).PP (levels 0).πP d (levels 0).σBase,
    D₀.Valid (levels 0).HBase (r+4) (levels 0).I (levels 0).J
      (gammaLoss*Fintype.card (levels 0).VP) (sigmaLoss*Fintype.card (levels 0).VP) →
    let E₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      (r+4) (levels 0).πP (3*d) ((levels 0).HBase false) ((levels 0).HBase true)=>markedWheelPhysicalResources W
    let B₀:=(D₀.remaining (levels 0).HBase).image (markedResourceEmbedding (chain.intoV 0).toEmbedding (chain.intoU 0));
    ∃ L:Finset (Finset (levels 0).VP⊕((levels 0).VP×(levels 0).UP)),L⊆B₀ ∧
      HasResourceDecomposition R₀ (B₀\L) ∧
      let last:=count-1
      let E:=MarkedSampleArc (levels last).PP (levels last).πP (3*d) (fun e=>(levels last).σBase (Sum.inl e)) false
      let K:=MarkedSampleArc (levels last).PP (levels last).πP (3*d) (fun e=>(levels last).σBase (Sum.inl e)) true
      let S:=Finset.univ.filter (fun z:(levels last).VP×(levels last).UP=>
        (levels last).HBase false z.1 z.2∨(levels last).HBase true z.1 z.2)
      let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        (levels last).πP Finset.univ S;
      L⊆((Full.filter (markedInnerResource (levels last).I (levels last).J)).image
        (markedResourceEmbedding (chain.intoV last).toEmbedding (chain.intoU last))) ∧
      MarkedReferenceTerminalRepresentation (levels last) (chain.intoV last).toEmbedding (chain.intoU last) L := by
  intro chain hsteps D₀ hD₀ E₀ K₀ R₀ B₀
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
  let State (i:ℕ):Type:=MarkedReferenceDeletion (levels i).PP (levels i).πP d (levels i).σBase
  let Good (i:ℕ) (D:State i):Prop:=D.Valid (levels i).HBase (r+4) (levels i).I (levels i).J
    (gammaLoss*Fintype.card (levels i).VP) (sigmaLoss*Fintype.card (levels i).VP)
  let B (i:ℕ) (D:State i):Finset (Finset (levels 0).VP⊕((levels 0).VP×(levels 0).UP)):=
    (D.remaining (levels i).HBase).image (markedResourceEmbedding (chain.intoV i).toEmbedding (chain.intoU i))
  have hStep:∀ i<count-1,∀ D:State i,Good i D →
      ∃ D':State (i+1),Good (i+1) D' ∧ B (i+1) D'⊆B i D ∧
        HasResourceDecomposition R₀ (B i D\B (i+1) D'):=by
    intro i hi D hD
    have hi' : i<count := by omega
    have hnext : i+1<count := by omega
    obtain ⟨L,hsub,hinner,hrep,hdec,hNext⟩:=hsteps i hi' D hD
    obtain ⟨D',hValid,hRem⟩:=hNext (levels (i+1)).VP (levels (i+1)).UP
      (chain.nextV i hnext) (chain.nextU i hnext) (levels (i+1)).πP
      (chain.nextComm i hnext) (chain.nextVimage i hnext) (chain.nextUimage i hnext)
      (levels (i+1)).I (levels (i+1)).J (chain.nextVdeeper i hnext) (chain.nextUdeeper i hnext)
    obtain ⟨D'',hEquiv,hRemov,hRemaining⟩:=marked_reference_state_transport
      ((levels i).PP.comap (chain.nextV i hnext)) (levels (i+1)).PP (levels (i+1)).πP d (r+4)
      (rawMarkedRestrictPair (chain.nextV i hnext) (chain.nextU i hnext) (levels i).σBase) (levels (i+1)).σBase
      (fun b v u=>(levels i).HBase b (chain.nextV i hnext v) (chain.nextU i hnext u)) (levels (i+1)).HBase
      (chain.nextGraph i hnext).symm (chain.nextOutcome i hnext).symm (chain.nextSpokes i hnext).symm
      (levels (i+1)).I (levels (i+1)).J (gammaLoss*(levels i).I.card) (sigmaLoss*(levels i).I.card) D'
    have hcard : (levels i).I.card=Fintype.card (levels (i+1)).VP := by
      rw [←chain.nextVimage i hnext,Finset.card_image_of_injective _ (chain.nextV i hnext).injective]
      simp
    have hGood:Good (i+1) D'' := by
      change D''.Valid _ _ _ _ _ _
      rw [←hcard]
      exact hEquiv.mpr hValid
    let nextR:=markedResourceEmbedding (chain.nextV i hnext).toEmbedding (chain.nextU i hnext)
    let curR:=markedResourceEmbedding (chain.intoV i).toEmbedding (chain.intoU i)
    let newR:=markedResourceEmbedding (chain.intoV (i+1)).toEmbedding (chain.intoU (i+1))
    have hf:(chain.nextV i hnext).toEmbedding.trans (chain.intoV i).toEmbedding=(chain.intoV (i+1)).toEmbedding:=by
      ext v
      exact (chain.composeV i hnext v).symm
    have hg:(chain.nextU i hnext).trans (chain.intoU i)=(chain.intoU (i+1)):=by
      ext u
      exact (chain.composeU i hnext u).symm
    have hmap:∀ z,curR (nextR z)=newR z:=by
      intro z
      dsimp only [curR,nextR,newR]
      rw [markedResourceEmbedding_comp_apply,hf,hg]
    have hBeq:B (i+1) D''=L.image curR:=by
      dsimp only [B]
      rw [hRemaining]
      change (D'.remaining _).image newR=L.image curR
      calc
        _ = (D'.remaining _).image (fun z=>curR (nextR z)) := by
          apply Finset.image_congr
          intro z _
          exact (hmap z).symm
        _ = ((D'.remaining _).image nextR).image curR := (Finset.image_image).symm
        _ = L.image curR := congrArg (fun U=>U.image curR) hRem
    have hsubset:B (i+1) D''⊆B i D := by rw [hBeq];exact Finset.image_subset_image hsub
    have hdecA:=marked_reference_level_decomposition_embedding levels chain i hi' (D.remaining (levels i).HBase\L) hdec
    have hdecA':HasResourceDecomposition R₀ (B i D\B (i+1) D''):=by
      rw [hBeq]
      change HasResourceDecomposition R₀ ((D.remaining _).image curR\L.image curR)
      rw [←Finset.image_sdiff _ _ curR.injective]
      exact hdecA
    exact ⟨D'',hGood,hsubset,hdecA'⟩
  obtain ⟨Dlast,hGood,hsub,hdec⟩:=reindexed_resource_iteration R₀ State B Good (count-1) hStep D₀ hD₀
  have hlast:count-1<count := by omega
  obtain ⟨L,hL,hInner,hrep,hLastDec,hNext⟩:=hsteps (count-1) hlast Dlast hGood
  let f:=markedResourceEmbedding (chain.intoV (count-1)).toEmbedding (chain.intoU (count-1))
  have hLsub:L.image f⊆B (count-1) Dlast:=Finset.image_subset_image hL
  have hnewdec:=marked_reference_level_decomposition_embedding levels chain (count-1) hlast (Dlast.remaining _\L) hLastDec
  have hnewdec':HasResourceDecomposition R₀ (B (count-1) Dlast\L.image f):=by
    change HasResourceDecomposition R₀ ((Dlast.remaining _).image f\L.image f)
    rw [←Finset.image_sdiff _ _ f.injective]
    exact hnewdec
  have hdis:Disjoint (B 0 D₀\B (count-1) Dlast) (B (count-1) Dlast\L.image f):=
    Finset.disjoint_left.mpr (fun _ ha hb=>(Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1)
  have hall:=resource_decomposition_union R₀ _ _ hdec hnewdec' hdis
  have heq:(B 0 D₀\B (count-1) Dlast)∪(B (count-1) Dlast\L.image f)=B 0 D₀\L.image f:=by
    ext z
    have hh:=fun hz=>hsub (x:=z) hz
    have hk:=fun hz=>hLsub (x:=z) hz
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [heq] at hall
  refine ⟨L.image f,hLsub.trans hsub,hall,?_,?_⟩
  · exact Finset.image_subset_image hInner
  · obtain ⟨AR,SR,hS,hAR,hSR,hDiv,hL⟩:=hrep
    unfold MarkedReferenceTerminalRepresentation
    dsimp only
    refine ⟨AR,SR,hS,hAR,hSR,hDiv,?_⟩
    exact congrArg (fun Z=>Z.image f) hL

end Oberwolfach
