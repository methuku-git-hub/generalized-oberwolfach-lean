module

public import Oberwolfach.MarkedReferenceLevelChain

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

def markedReferenceBoundedIndex (count i:ℕ):ℕ:=if i<count then i else 0

theorem marked_reference_bounded_index_lt (count i:ℕ) (hcount:0<count):
    markedReferenceBoundedIndex count i<count:=by
  unfold markedReferenceBoundedIndex
  split_ifs <;> omega

theorem marked_reference_bounded_index_eq (count i:ℕ) (hi:i<count):
    markedReferenceBoundedIndex count i=i:=by
  simp [markedReferenceBoundedIndex,hi]

variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
variable (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
variable [∀ i,Fintype (levels i).VP] [∀ i,Fintype (levels i).UP]
  [∀ i,LinearOrder (levels i).VP] [∀ i,DecidableEq (levels i).UP]
variable {count:ℕ} (chain:MarkedReferenceLevelChain levels count)

abbrev markedReferenceBoundedVertexType (i:ℕ):Type:=(levels (markedReferenceBoundedIndex count i)).VP

abbrev markedReferenceBoundedHubType (i:ℕ):Type:=(levels (markedReferenceBoundedIndex count i)).UP

def markedReferenceBoundedVertexEmbedding (i:ℕ):
    markedReferenceBoundedVertexType levels (count:=count) i ↪o (levels 0).VP:=
  chain.intoV (markedReferenceBoundedIndex count i)

def markedReferenceBoundedHubEmbedding (i:ℕ):
    markedReferenceBoundedHubType levels (count:=count) i ↪ (levels 0).UP:=
  chain.intoU (markedReferenceBoundedIndex count i)

def markedReferenceBoundedPermutation (i:ℕ):
    Equiv.Perm (markedReferenceBoundedVertexType levels (count:=count) i):=
  (levels (markedReferenceBoundedIndex count i)).πP

theorem marked_reference_bounded_ambient_comm (hcount:0<count) (i:ℕ)
    (v:markedReferenceBoundedVertexType levels (count:=count) i):
    markedReferenceBoundedVertexEmbedding levels chain i (markedReferenceBoundedPermutation levels (count:=count) i v)=
      (levels 0).πP (markedReferenceBoundedVertexEmbedding levels chain i v):=by
  exact chain.ambientComm (markedReferenceBoundedIndex count i)
    (marked_reference_bounded_index_lt count i hcount) v
end Oberwolfach
