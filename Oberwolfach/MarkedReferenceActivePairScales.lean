module

public import Oberwolfach.MarkedReferenceChainActiveScales
public import Oberwolfach.VortexRemovedStarScales

@[expose] public section
/-! The deeper sets of one reference level are the images of the inner
sets of the next. Thus their cardinalities give the actual geometric decay
of the fixed reference domains, without an additional sampling assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 10000000
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

theorem marked_reference_active_pair_scales
    (chain:MarkedReferenceLevelChain levels count) (L:ℕ) (hL:L+1≤count)
    (hcut0:0≤hIcut) (hcut1:hIcut<1):
    (∀ i,i<L→((((levels (i+1)).I)\((levels (i+1)).T)).card:ℝ)≤
      (hIcut/(1-hIcut))*((((levels i).I)\((levels i).T)).card:ℝ)) ∧
    (∀ i,i<L→((((levels (i+1)).J)\((levels (i+1)).Wrem)).card:ℝ)≤
      (hIcut/(1-hIcut))*((((levels i).J)\((levels i).Wrem)).card:ℝ)) ∧
    (∀ i,i≤L→∀ v,(levels i).πP v∈(levels i).I\(levels i).T ↔
      v∈(levels i).I\(levels i).T):=by
  let W:=fun i=>(levels i).VP
  let Z:=fun i=>(levels i).UP
  let I:=fun i=>(levels i).I
  let T:=fun i=>(levels i).T
  let J:=fun i=>(levels i).J
  let Wrem:=fun i=>(levels i).Wrem
  have hsubI:∀ i,i≤L→T i⊆I i:=fun i _=>(levels i).hTI
  have hsubJ:∀ i,i≤L→Wrem i⊆J i:=fun i _=>(levels i).hWremJ
  have hsmallI:∀ i,i≤L→((T i).card:ℝ)≤hIcut*(I i).card:=fun i _=>(levels i).hTcut
  have hsmallJ:∀ i,i≤L→((Wrem i).card:ℝ)≤hIcut*(J i).card:=fun i _=>(levels i).hWcut
  have hstepI:∀ i,i<L→((I (i+1)).card:ℝ)≤hIcut*(I i).card:=by
    intro i hi
    exact (marked_reference_next_inner_scales levels chain i (by omega)).1
  have hstepJ:∀ i,i<L→((J (i+1)).card:ℝ)≤hIcut*(J i).card:=by
    intro i hi
    exact (marked_reference_next_inner_scales levels chain i (by omega)).2
  have hsI:=vortex_sdiff_scales W I T L hIcut hIcut hcut0 hcut1 hcut0 hsubI hsmallI hstepI
  have hsJ:=vortex_sdiff_scales Z J Wrem L hIcut hIcut hcut0 hcut1 hcut0 hsubJ hsmallJ hstepJ
  refine ⟨hsI.2,hsJ.2,?_⟩
  intro i hi v
  simp only [Finset.mem_sdiff,(levels i).hI v,(levels i).hT v]
end Oberwolfach
