module

public import Oberwolfach.OrdinaryVortexNondeeperDomains
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! A nondeeper domain embeds in its own parent and both embeddings compose
to the already fixed physical vertex and hub embeddings. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε m)

def ordinaryNondeeperVertexToParent (i:ℕ):
    ordinaryVortexNondeeperVertexType Q i↪markedVortexVertexType Q i where
  toFun x:=⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩
  inj' :=by
    intro x y h
    have hh:x.val=y.val:=congrArg (fun z:markedVortexVertexType Q i=>z.val) h
    exact Subtype.ext hh

def ordinaryNondeeperHubToParent (i:ℕ):
    ordinaryVortexNondeeperHubType Q i↪markedVortexHubType Q i where
  toFun x:=⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩
  inj' :=by
    intro x y h
    have hh:x.val=y.val:=congrArg (fun z:markedVortexHubType Q i=>z.val) h
    exact Subtype.ext hh

theorem ordinary_nondeeper_vertex_embedding_composition (i:ℕ):
    (ordinaryNondeeperVertexToParent Q i).trans (markedVortexVertexEmbedding Q i).toEmbedding=
      ordinaryVortexNondeeperVertexEmbedding Q i :=by
  ext x
  rfl

theorem ordinary_nondeeper_hub_embedding_composition (i:ℕ):
    (ordinaryNondeeperHubToParent Q i).trans (markedVortexHubEmbedding Q i)=
      ordinaryVortexNondeeperHubEmbedding Q i :=by
  ext x
  rfl
end Oberwolfach
