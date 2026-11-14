module

public import Oberwolfach.MarkedReferenceLevelChain

@[expose] public section

/-! Embed every typed occurrence and every wheel from a fixed vortex
reference into the first reference, preserving the actual physical rim and
spoke resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
variable (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
variable [∀ i,Fintype (levels i).VP] [∀ i,Fintype (levels i).UP]
  [∀ i,LinearOrder (levels i).VP] [∀ i,DecidableEq (levels i).UP]
variable {count:ℕ} (chain:MarkedReferenceLevelChain levels count)

def markedReferenceLevelArcEmbedding (i:ℕ) (hi:i<count) (j:Bool):
    MarkedSampleArc (levels i).PP (levels i).πP (3*d) (fun e=>(levels i).σBase (Sum.inl e)) j ↪
      MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) j where
  toFun a := ⟨(chain.intoV i a.val.1,chain.intoV i a.val.2),by
    let a0 : (levels i).VP×(levels i).VP := a.val
    have ha : markedPhysicalRim (levels i).PP (levels i).πP (3*d)
        (fun e=>(levels i).σBase (Sum.inl e)) j a0.1 a0.2=1 := a.property
    rw [chain.ambientGraph i hi,chain.ambientOutcome i hi] at ha
    exact (markedPhysicalRim_orderEmbedding (chain.intoV i) (levels 0).πP (levels i).πP
      (chain.ambientComm i hi) (levels 0).PP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) j a.val.1 a.val.2).mp ha⟩
  inj' a b hab := by
    apply Subtype.ext
    apply Prod.ext
    · exact (chain.intoV i).injective (congrArg (fun z=>z.val.1) hab)
    · exact (chain.intoV i).injective (congrArg (fun z=>z.val.2) hab)

theorem markedReferenceLevelArcEmbedding_endpoints (i:ℕ) (hi:i<count) (j:Bool)
    (a:MarkedSampleArc (levels i).PP (levels i).πP (3*d) (fun e=>(levels i).σBase (Sum.inl e)) j):
    (markedReferenceLevelArcEmbedding levels chain i hi j a).val = (chain.intoV i a.val.1,chain.intoV i a.val.2):=rfl

theorem marked_reference_level_decomposition_embedding (i:ℕ) (hi:i<count)
    (S:Finset (Finset (levels i).VP⊕((levels i).VP×(levels i).UP))) :
    let Ei:=MarkedSampleArc (levels i).PP (levels i).πP (3*d) (fun e=>(levels i).σBase (Sum.inl e)) false
    let Ki:=MarkedSampleArc (levels i).PP (levels i).πP (3*d) (fun e=>(levels i).σBase (Sum.inl e)) true
    let E₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true;
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:Ei=>e.val.1) (fun e=>e.val.2) (fun e:Ki=>e.val.1) (fun e=>e.val.2)
        (r+4) (levels i).πP (3*d) ((levels i).HBase false) ((levels i).HBase true)=>markedWheelPhysicalResources W) S →
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
        (r+4) (levels 0).πP (3*d) ((levels 0).HBase false) ((levels 0).HBase true)=>markedWheelPhysicalResources W)
      (S.image (markedResourceEmbedding (chain.intoV i).toEmbedding (chain.intoU i))):=by
  intro Ei Ki E₀ K₀ hS
  let e:=markedReferenceLevelArcEmbedding levels chain i hi false
  let k:=markedReferenceLevelArcEmbedding levels chain i hi true
  have he (a:Ei):(e a).val=(chain.intoV i a.val.1,chain.intoV i a.val.2):=
    markedReferenceLevelArcEmbedding_endpoints levels chain i hi false a
  have hk (a:Ki):(k a).val=(chain.intoV i a.val.1,chain.intoV i a.val.2):=
    markedReferenceLevelArcEmbedding_endpoints levels chain i hi true a
  apply marked_resource_decomposition_embedding (H₀:=(levels i).HBase false) (HK:=(levels i).HBase true) (chain.intoV i).toEmbedding (chain.intoU i)
    (chain.ambientComm i hi) e k
    (fun a=>congrArg Prod.fst (he a)) (fun a=>congrArg Prod.snd (he a))
    (fun a=>congrArg Prod.fst (hk a)) (fun a=>congrArg Prod.snd (hk a))
  · intro v u hv
    rw [chain.ambientSpokes i hi] at hv
    exact hv
  · intro v u hv
    rw [chain.ambientSpokes i hi] at hv
    exact hv
  · exact hS

end Oberwolfach
