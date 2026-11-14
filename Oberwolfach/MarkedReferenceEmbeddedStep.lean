module

public import Oberwolfach.MarkedReferenceFiniteIteration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
theorem marked_reference_embedded_iteration_step
    (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (count:ℕ) (hcount:0<count) (gammaLoss sigmaLoss:ℝ):
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ chain:MarkedReferenceLevelChain levels count,
    (∀ i,i<count → MarkedReferenceLevelStepProperty (levels i) gammaLoss sigmaLoss) →
    let State:=fun i=>MarkedReferenceDeletion (levels i).PP (levels i).πP d (levels i).σBase
    let Good:=fun i (D:State i)=>D.Valid (levels i).HBase (r+4) (levels i).I (levels i).J
      (gammaLoss*Fintype.card (levels i).VP) (sigmaLoss*Fintype.card (levels i).VP)
    let B:=fun i (D:State i)=>(D.remaining (levels i).HBase).image
      (markedResourceEmbedding (chain.intoV i).toEmbedding (chain.intoU i))
    let E₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      (r+4) (levels 0).πP (3*d) ((levels 0).HBase false) ((levels 0).HBase true)=>markedWheelPhysicalResources W;
    ∀ i<count-1,∀ D:State i,Good i D →
      ∃ D':State (i+1),Good (i+1) D' ∧ B (i+1) D'⊆B i D ∧
        HasResourceDecomposition R₀ (B i D\B (i+1) D')
:= by
  intro chain hsteps State Good B E₀ K₀ R₀
  letI : ∀ i,Fintype (levels i).VP := fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP := fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP := fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP := fun i=>(levels i).inst10
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
end Oberwolfach
