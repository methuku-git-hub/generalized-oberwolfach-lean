module

public import Oberwolfach.MarkedReferenceBoundedEnumeration
public import Oberwolfach.MarkedReferenceChainActiveScales

@[expose] public section
/-! Extend a finite, nonempty reference chain to all natural indices by
repeating level zero outside the chain. The sampled event still concerns
only its declared fixed levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 12000000
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


def markedReferenceBoundedInner (i:ℕ):Finset (markedReferenceBoundedVertexType levels (count:=count) i):=
  (levels (markedReferenceBoundedIndex count i)).I

def markedReferenceBoundedDeeper (i:ℕ):Finset (markedReferenceBoundedVertexType levels (count:=count) i):=
  (levels (markedReferenceBoundedIndex count i)).T

def markedReferenceBoundedHubInner (i:ℕ):Finset (markedReferenceBoundedHubType levels (count:=count) i):=
  (levels (markedReferenceBoundedIndex count i)).J

def markedReferenceBoundedHubDeeper (i:ℕ):Finset (markedReferenceBoundedHubType levels (count:=count) i):=
  (levels (markedReferenceBoundedIndex count i)).Wrem

theorem marked_reference_bounded_geometry (hcount:0<count) (i:ℕ):
    markedReferenceBoundedDeeper levels (count:=count) i⊆markedReferenceBoundedInner levels (count:=count) i ∧
    markedReferenceBoundedHubDeeper levels (count:=count) i⊆markedReferenceBoundedHubInner levels (count:=count) i ∧
    (((markedReferenceBoundedDeeper levels (count:=count) i).card:ℝ)≤hIcut*(markedReferenceBoundedInner levels (count:=count) i).card) ∧
    (((markedReferenceBoundedHubDeeper levels (count:=count) i).card:ℝ)≤hIcut*(markedReferenceBoundedHubInner levels (count:=count) i).card) ∧
    (∀ v,markedReferenceBoundedPermutation levels (count:=count) i v∈markedReferenceBoundedInner levels (count:=count) i ↔
      v∈markedReferenceBoundedInner levels (count:=count) i) ∧
    (∀ v,markedReferenceBoundedPermutation levels (count:=count) i v∈markedReferenceBoundedDeeper levels (count:=count) i ↔
      v∈markedReferenceBoundedDeeper levels (count:=count) i):=by
  exact ⟨(levels (markedReferenceBoundedIndex count i)).hTI,
    (levels (markedReferenceBoundedIndex count i)).hWremJ,
    (levels (markedReferenceBoundedIndex count i)).hTcut,
    (levels (markedReferenceBoundedIndex count i)).hWcut,
    (levels (markedReferenceBoundedIndex count i)).hI,
    (levels (markedReferenceBoundedIndex count i)).hT⟩

theorem marked_reference_bounded_next_inner_scales
    (chain:MarkedReferenceLevelChain levels count) (i:ℕ) (hi:i+1<count):
    (((markedReferenceBoundedInner levels (count:=count) (i+1)).card:ℝ)≤
      hIcut*(markedReferenceBoundedInner levels (count:=count) i).card) ∧
    (((markedReferenceBoundedHubInner levels (count:=count) (i+1)).card:ℝ)≤
      hIcut*(markedReferenceBoundedHubInner levels (count:=count) i).card):=by
  have hi0:i<count:=by omega
  have hI1:((markedReferenceBoundedInner levels (count:=count) (i+1)).card:ℝ)=((levels (i+1)).I.card:ℝ):=by
    exact congrArg (fun j:ℕ=>((levels j).I.card:ℝ)) (marked_reference_bounded_index_eq count (i+1) hi)
  have hI0:((markedReferenceBoundedInner levels (count:=count) i).card:ℝ)=((levels i).I.card:ℝ):=by
    exact congrArg (fun j:ℕ=>((levels j).I.card:ℝ)) (marked_reference_bounded_index_eq count i hi0)
  have hJ1:((markedReferenceBoundedHubInner levels (count:=count) (i+1)).card:ℝ)=((levels (i+1)).J.card:ℝ):=by
    exact congrArg (fun j:ℕ=>((levels j).J.card:ℝ)) (marked_reference_bounded_index_eq count (i+1) hi)
  have hJ0:((markedReferenceBoundedHubInner levels (count:=count) i).card:ℝ)=((levels i).J.card:ℝ):=by
    exact congrArg (fun j:ℕ=>((levels j).J.card:ℝ)) (marked_reference_bounded_index_eq count i hi0)
  rw [hI1,hI0,hJ1,hJ0]
  exact marked_reference_next_inner_scales levels chain i hi
end Oberwolfach
