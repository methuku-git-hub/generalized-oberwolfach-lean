module

public import Oberwolfach.MarkedReferenceLevelStepProperty
public import Oberwolfach.MarkedSampleArcEmbedding
public import Oberwolfach.MarkedResourceDecompositionEmbedding
public import Oberwolfach.MarkedReferenceStateTransport

@[expose] public section

/-! A fixed sequence of nested reference graphs and their actual restrictions.
The equalities express compatibility of the prescribed sample and spoke
relations; no sampling law or cover-down packing is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 18000000
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

structure MarkedReferenceLevelChain (count:ℕ) where
  nextV : ∀ i,i+1<count → (levels (i+1)).VP ↪o (levels i).VP
  nextU : ∀ i,i+1<count → (levels (i+1)).UP ↪ (levels i).UP
  intoV : ∀ i,(levels i).VP ↪o (levels 0).VP
  intoU : ∀ i,(levels i).UP ↪ (levels 0).UP
  nextComm : ∀ i (hi:i+1<count) v,nextV i hi ((levels (i+1)).πP v)=(levels i).πP (nextV i hi v)
  ambientComm : ∀ i (hi:i<count) v,intoV i ((levels i).πP v)=(levels 0).πP (intoV i v)
  nextVimage : ∀ i (hi:i+1<count),Finset.univ.image (nextV i hi)=(levels i).I
  nextUimage : ∀ i (hi:i+1<count),Finset.univ.image (nextU i hi)=(levels i).J
  nextVdeeper : ∀ i (hi:i+1<count) v,nextV i hi v∈(levels i).T ↔ v∈(levels (i+1)).I
  nextUdeeper : ∀ i (hi:i+1<count) u,nextU i hi u∈(levels i).Wrem ↔ u∈(levels (i+1)).J
  nextGraph : ∀ i (hi:i+1<count),(levels (i+1)).PP=(levels i).PP.comap (nextV i hi)
  nextOutcome : ∀ i (hi:i+1<count),(levels (i+1)).σBase=rawMarkedRestrictPair (nextV i hi) (nextU i hi) (levels i).σBase
  nextSpokes : ∀ i (hi:i+1<count),(levels (i+1)).HBase=fun b v u=>(levels i).HBase b (nextV i hi v) (nextU i hi u)
  ambientGraph : ∀ i (hi:i<count),(levels i).PP=(levels 0).PP.comap (intoV i)
  ambientOutcome : ∀ i (hi:i<count),(levels i).σBase=rawMarkedRestrictPair (intoV i) (intoU i) (levels 0).σBase
  ambientSpokes : ∀ i (hi:i<count),(levels i).HBase=fun b v u=>(levels 0).HBase b (intoV i v) (intoU i u)
  composeV : ∀ i (hi:i+1<count) v,intoV (i+1) v=intoV i (nextV i hi v)
  composeU : ∀ i (hi:i+1<count) u,intoU (i+1) u=intoU i (nextU i hi u)
  firstV : ∀ v,intoV 0 v=v
  firstU : ∀ u,intoU 0 u=u

end Oberwolfach
