module

public import Oberwolfach.MarkedVortexActiveDomainEquivalences
public import Oberwolfach.MarkedVortexActivePermutation

@[expose] public section
/-! The next active vertex set embeds in the parent with its deeper vertices
removed. The composition into the original graph is the next active embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

abbrev markedVortexNonDeeperVertexType (i:ℕ):Type:=
  ↥((Finset.univ\markedVortexDeeperVertices Q i):Finset (markedVortexVertexType Q i))

def markedVortexNonDeeperVertexEmbedding (i:ℕ):
    markedVortexNonDeeperVertexType Q i ↪o markedVortexVertexType Q i where
  toFun:=Subtype.val
  inj':=Subtype.val_injective
  map_rel_iff':=by intro x y;rfl

def markedVortexNextActiveInNonDeeper (i:ℕ):
    ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))) ↪o
      markedVortexNonDeeperVertexType Q i where
  toFun x:=⟨⟨x.val.val,(Q.extendedVertices_subset (Nat.le_succ i)) x.val.property⟩,by
    have hx: x.val∉markedVortexInnerVertices Q (i+1):=(Finset.mem_sdiff.mp x.property).2
    have hnot:x.val.val∉Q.extendedVertices (i+2):=by
      simpa [markedVortexInnerVertices,Nat.add_assoc] using hx
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,markedVortexDeeperVertices,Finset.mem_filter]
    simpa using hnot⟩
  inj':=by intro x y h;apply Subtype.ext;apply Subtype.ext;exact congrArg (fun z=>z.val.val) h
  map_rel_iff':=by intro x y;rfl

theorem marked_vortex_next_active_embedding_composition (i:ℕ)
    (x:↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1)))):
    markedVortexVertexEmbedding Q i (markedVortexNonDeeperVertexEmbedding Q i (markedVortexNextActiveInNonDeeper Q i x))=
      markedVortexActiveVertexEmbedding Q (i+1) x:=rfl
end Oberwolfach
