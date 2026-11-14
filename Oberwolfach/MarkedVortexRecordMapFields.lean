module

public import Oberwolfach.MarkedVortexNonDeeperImages
public import Oberwolfach.MarkedVortexLevelPermutationFields
public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! The actual record maps use the same physical vertex and hub coordinates,
including the nested active embedding and its permutation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_record_map_fields
    (he:0≤ε) (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    let VP:=markedVortexVertexType Q i
    let A:=markedVortexNonDeeperVertexType Q i
    let B:=markedVortexNonDeeperHubType Q i
    let W:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
      Finset (markedVortexVertexType Q (i+1)))
    let fA:=markedVortexNonDeeperVertexEmbedding Q i
    let gA:=markedVortexNonDeeperHubToParent Q i
    let f:=markedVortexNextActiveInNonDeeper Q i
    let πP:=markedVortexPermutation Q π hπ i
    let πA:=markedVortexNonDeeperPermutation Q π hπ i
    let ρ:=markedVortexActivePermutation Q π hπ (i+1)
    let I:=markedVortexInnerVertices Q i
    let J:=markedVortexInnerHubs Q i
    let T:=markedVortexDeeperVertices Q i
    let R:=markedVortexDeeperHubs Q i
    let X:=Finset.univ.image f
    let Z:=markedVortexInnerNonDeeperHubs Q i;
    (∀ x:A,fA (πA x)=πP (fA x)) ∧
    (∀ x:W,f (ρ x)=πA (f x)) ∧
    (∀ x:VP,πP x∈I↔x∈I) ∧ (∀ x:VP,πP x∈T↔x∈T) ∧
    (∀ x:A,πA x∈X↔x∈X) ∧
    (Finset.univ.image fA=Finset.univ\T) ∧
    (Finset.univ.image gA=Finset.univ\R) ∧
    X.image fA=I\T ∧ Z.image gA=J\R ∧ T⊆I ∧ R⊆J ∧
    (∀ x:W,markedVortexVertexEmbedding Q i (fA (f x))=
      markedVortexActiveVertexEmbedding Q (i+1) x) ∧
    (∀ u:B,markedVortexHubEmbedding Q i (gA u)=markedVortexNonDeeperHubToPhysical Q i u) := by
  intro VP A B W fA gA f πP πA ρ I J T R X Z
  have hp:=marked_vortex_permutation_compatibility Q π hπ i
  have himages:=marked_vortex_nondeeper_parent_images Q i
  have hgeom:=marked_vortex_fixed_active_geometry Q he i
  refine ⟨marked_vortex_nondeeper_permutation_embedding Q π hπ i,
    marked_vortex_next_active_permutation_commutes Q π hπ i,
    hp.2.1,hp.2.2,marked_vortex_next_active_image_invariant Q π hπ i,
    himages.1,himages.2,?_,marked_vortex_inner_nondeeper_hubs_image Q i,
    hgeom.1,hgeom.2.1,marked_vortex_next_active_embedding_composition Q i,fun _=>rfl⟩
  dsimp [X]
  rw [Finset.image_image]
  exact marked_vortex_next_active_parent_image Q i
end Oberwolfach
