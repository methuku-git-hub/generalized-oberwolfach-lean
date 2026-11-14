module

public import Oberwolfach.MarkedCommonNamedWeightedActualDensity

@[expose] public section
/-! Preserve the selected level weight and matching continuation while
packaging the actual parent and active weights for the same-sample selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchingSampleSelectorFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [Nonempty (Fin n)] [DecidableEq U]
local notation "V" => Fin n
theorem marked_matching_sample_supplies_weighted_selector
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Bool→ℝ) (s:U→Bool→ℝ)
    (sizeCorr aCorr bCorr eCorr fCorr:ℕ) (εCorr ζCorr ξCorr:ℝ)
    (mass:MarkedExpandedActualOutcome (U:=U) π d→ℝ)
    (Common:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (levelOK:(∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)→Prop)
    (Prior Tail:(∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)→
      MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (hMatching:∃ (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ),
      ∃ hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i),
      ∃ hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i),
      ∃ levelWeight,levelOK levelWeight ∧
      ∃ outcome,0<mass outcome ∧ Prior levelWeight outcome ∧
      (MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome)) ∧ Common outcome ∧ (MarkedProtectedAbsorbableCorrectionWithBounds G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr (markedExpandedActualSelected π d outcome).1
      (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1)) ∧ Tail levelWeight outcome):
    ∃ (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ),
      ∃ hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i),
      ∃ hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i),
      ∃ outcome,0<mass outcome ∧ (∃ levelWeight,levelOK levelWeight ∧ Prior levelWeight outcome ∧ Tail levelWeight outcome) ∧
      (MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome)) ∧ Common outcome ∧ (MarkedProtectedAbsorbableCorrectionWithBounds G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr (markedExpandedActualSelected π d outcome).1
      (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1)) := by
  obtain ⟨weightParent,weight,hParentWeight,hActiveWeight,levelWeight,hLevel,outcome,hMass,hPrior,hParent,hCommon,hCorr,hTail⟩:=hMatching
  exact ⟨weightParent,weight,hParentWeight,hActiveWeight,outcome,hMass,⟨levelWeight,hLevel,hPrior,hTail⟩,hParent,hCommon,hCorr⟩
end Oberwolfach
