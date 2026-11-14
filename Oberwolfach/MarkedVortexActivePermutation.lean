module

public import Oberwolfach.MarkedNestedVortexActiveWeights
public import Oberwolfach.InvariantPermutation

@[expose] public section
/-! Restrict the original permutation to each fixed active vortex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

def markedVortexActivePermutation (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    Equiv.Perm (↑(Finset.univ\markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i)):=
  invariantSetPermutation (markedVortexPermutation Q π hπ i) _ (by
    intro x
    simp only [Finset.mem_coe,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact not_congr ((marked_vortex_permutation_compatibility Q π hπ i).2.1 x))

theorem marked_vortex_active_permutation_to_physical (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ)
    (x:{x:markedVortexVertexType Q i // x∈Finset.univ\markedVortexInnerVertices Q i}):
    ((markedVortexActivePermutation Q π hπ i x).val.val)=π x.val.val:=rfl

def markedVortexActiveVertexEmbedding (i:ℕ):
    {x:markedVortexVertexType Q i // x∈Finset.univ\markedVortexInnerVertices Q i} ↪o V where
  toFun x:=x.val.val
  inj':=by intro x y h;apply Subtype.ext;apply Subtype.ext;exact h
  map_rel_iff':=by intro x y;rfl

def markedVortexActiveHubEmbedding (i:ℕ):
    {u:markedVortexHubType Q i // u∈Finset.univ\markedVortexInnerHubs Q i} ↪ U where
  toFun u:=u.val.val
  inj':=by intro x y h;apply Subtype.ext;apply Subtype.ext;exact h

theorem marked_vortex_active_permutation_embedding (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ)
    (x:{x:markedVortexVertexType Q i // x∈Finset.univ\markedVortexInnerVertices Q i}):
    markedVortexActiveVertexEmbedding Q i (markedVortexActivePermutation Q π hπ i x)=
      π (markedVortexActiveVertexEmbedding Q i x):=rfl

end Oberwolfach
