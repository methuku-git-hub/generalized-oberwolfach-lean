module

public import Oberwolfach.MarkedReferenceLevelChain

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

theorem marked_reference_next_inner_images (i:ℕ) (hi:i+1<count):
    (levels (i+1)).I.image (chain.nextV i hi)=(levels i).T ∧
    (levels (i+1)).J.image (chain.nextU i hi)=(levels i).Wrem:=by
  constructor
  · ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
      exact (chain.nextVdeeper i hi w).2 hw
    · intro hv
      have hvI:v∈(levels i).I:=(levels i).hTI hv
      rw [←chain.nextVimage i hi] at hvI
      obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp hvI
      exact Finset.mem_image.mpr ⟨w,(chain.nextVdeeper i hi w).1 hv,rfl⟩
  · ext u
    constructor
    · intro hu
      obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hu
      exact (chain.nextUdeeper i hi w).2 hw
    · intro hu
      have huJ:u∈(levels i).J:=(levels i).hWremJ hu
      rw [←chain.nextUimage i hi] at huJ
      obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp huJ
      exact Finset.mem_image.mpr ⟨w,(chain.nextUdeeper i hi w).1 hu,rfl⟩

theorem marked_reference_next_inner_cardinalities (chain:MarkedReferenceLevelChain levels count) (i:ℕ) (hi:i+1<count):
    (levels (i+1)).I.card=(levels i).T.card ∧
    (levels (i+1)).J.card=(levels i).Wrem.card:=by
  obtain ⟨hI,hJ⟩:=marked_reference_next_inner_images levels chain i hi
  constructor
  · rw [←hI,Finset.card_image_of_injective _ (chain.nextV i hi).injective]
  · rw [←hJ,Finset.card_image_of_injective _ (chain.nextU i hi).injective]

theorem marked_reference_next_inner_scales (chain:MarkedReferenceLevelChain levels count) (i:ℕ) (hi:i+1<count):
    (((levels (i+1)).I.card:ℝ)≤hIcut*(levels i).I.card) ∧
    (((levels (i+1)).J.card:ℝ)≤hIcut*(levels i).J.card):=by
  obtain ⟨hI,hJ⟩:=marked_reference_next_inner_cardinalities levels chain i hi
  rw [hI,hJ]
  exact ⟨(levels i).hTcut,(levels i).hWcut⟩
end Oberwolfach
