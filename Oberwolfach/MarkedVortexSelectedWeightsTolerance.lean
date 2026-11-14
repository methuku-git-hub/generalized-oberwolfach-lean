module

public import Oberwolfach.SuccessorWeightToleranceMono
public import Oberwolfach.MarkedVortexWeightFamiliesWeakenMargin

@[expose] public section
/-! Instantiate both weight-family hypotheses with the actual selector's
same functions and then weaken their common tolerance to the chain's two
later tolerances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_selected_weights_weaken_tolerances
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r k₀ d L:ℕ) (α δparent τParent τ:ℝ)
    (hρ:0 < initialIndexDensity U D) (hτParent:δparent≤τParent) (hτ:δparent≤τ)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (hParent:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      δparent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i))
    (hActive:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      δparent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)):
    (∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i)) ∧
    (∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)):=by
  constructor
  · intro i hi
    apply successor_sequence_weights_weaken_tolerance _ _ _ _ δparent _ _ _ _ (by positivity) hτParent
    exact hParent i hi
  · intro i hi
    apply successor_sequence_weights_weaken_tolerance _ _ _ _ δparent _ _ _ _ (by positivity) hτ
    exact hActive i hi
end Oberwolfach
