module

public import Oberwolfach.OrdinaryFixedVortexRowsIndices

@[expose] public section
/-! Named ordinary row and hub tests on all nonterminal levels of a fixed
vortex and one raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryFixedVortexRowIndexEvent
    (h d:ℕ) (εR εH:ℝ) (P F:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (p pH:ℝ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀i,i<Q.length→
    RawOrdinaryRows (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
      (markedVortexInnerVertices Q i) p (fun z=>s (markedVortexHubEmbedding Q i z)) j
      (εR*(markedVortexInnerVertices Q i).card)
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) ∧
    RawOrdinaryDomainIndices (F.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d h
      (markedVortexInnerHubs Q i) pH j (εH*(markedVortexInnerHubs Q i).card)
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)
end Oberwolfach
