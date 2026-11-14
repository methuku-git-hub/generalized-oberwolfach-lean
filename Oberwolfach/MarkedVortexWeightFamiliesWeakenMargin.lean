module

public import Oberwolfach.SuccessorWeightParameterMono
public import Oberwolfach.MarkedVortexCorrectedReferenceChain

@[expose] public section
/-! The parent and active weight families are fixed before sampling and
remain the same when the level chain uses a smaller density margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_weight_families_weaken_margin
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r k₀ d L:ℕ) (α α' τParent τ:ℝ) (hα:0<α') (hle:α'≤α)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (hParent:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i))
    (hActive:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)):
    (∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α'/4)) (successorWeightUpper k₀ (α'/4)) (weightParent i)) ∧
    (∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α'/4)) (successorWeightUpper k₀ (α'/4)) (weight i)):=by
  have hp:0<α'/4:=by positivity
  have hab:α'/4≤α/4:=by linarith
  constructor
  · intro i hi
    exact successor_sequence_weights_weaken_margin _ _ _ k₀ _ _ (α'/4) (α/4) _ hp hab (hParent i hi)
  · intro i hi
    exact successor_sequence_weights_weaken_margin _ _ _ k₀ _ _ (α'/4) (α/4) _ hp hab (hActive i hi)
end Oberwolfach
