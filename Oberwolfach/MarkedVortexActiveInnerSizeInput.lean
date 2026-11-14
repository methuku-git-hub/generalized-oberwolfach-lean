module

public import Oberwolfach.MarkedVortexInnerUpperSizeInputs
public import Oberwolfach.MarkedVortexSmallRemainderInputs
public import Oberwolfach.MarkedVortexNonDeeperInnerHubs
public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! The active inner vertex and hub sets are small relative to the
non-deeper vertex domain at each actual vortex level. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_active_inner_size_input
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (hehalf:ε≤1/2)
    (ξ:ℝ) (hξ:4*ε≤ξ) (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let Vkeep:=markedVortexNonDeeperVertexType Q i
      let X:=Finset.univ.image (markedVortexNextActiveInNonDeeper Q i)
      let Z:=markedVortexInnerNonDeeperHubs Q i
      ((ordinaryInnerVertices X Z).card:ℝ)≤ξ*Fintype.card Vkeep:=by
  intro i hi Vkeep X Z
  let VP:=markedVortexVertexType Q i
  let I:=markedVortexInnerVertices Q i
  let J:=markedVortexInnerHubs Q i
  let T:=markedVortexDeeperVertices Q i
  let R:=markedVortexDeeperHubs Q i
  have hupper:=marked_vortex_inner_upper_size_inputs Q hreg hn hD hρhi he ε le_rfl L hL i hi
  have hsmall:=marked_vortex_small_remainder_inputs Q hreg hn hD hρhi he hehalf ε ε ε le_rfl le_rfl le_rfl L hL i hi
  have hhalf:(Fintype.card VP:ℝ)/2≤Fintype.card Vkeep:=hsmall.2.2.2.2.2.2
  have hX:X.card≤I.card:=by
    have himage:X.image (markedVortexNonDeeperVertexEmbedding Q i)=I\T:=by
      dsimp [X]
      rw [Finset.image_image]
      exact marked_vortex_next_active_parent_image Q i
    have hh:=congrArg Finset.card himage
    rw [Finset.card_image_of_injective _ (markedVortexNonDeeperVertexEmbedding Q i).injective] at hh
    exact hh ▸ Finset.card_le_card (by intro x hx;exact (Finset.mem_sdiff.mp hx).1 : I\T⊆I)
  have hZ:Z.card≤J.card:=by
    have himage:Z.image (markedVortexNonDeeperHubToParent Q i)=J\R:=marked_vortex_inner_nondeeper_hubs_image Q i
    have hh:=congrArg Finset.card himage
    rw [Finset.card_image_of_injective _ (markedVortexNonDeeperHubToParent Q i).injective] at hh
    exact hh ▸ Finset.card_le_card (by intro x hx;exact (Finset.mem_sdiff.mp hx).1 : J\R⊆J)
  have hunion:(ordinaryInnerVertices X Z).card≤X.card+Z.card:=by
    unfold ordinaryInnerVertices
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))
  have hs:((ordinaryInnerVertices X Z).card:ℝ)≤2*ε*Fintype.card VP:=by
    have hx:(X.card:ℝ)≤I.card:=by exact_mod_cast hX
    have hz:(Z.card:ℝ)≤J.card:=by exact_mod_cast hZ
    have hu:((ordinaryInnerVertices X Z).card:ℝ)≤X.card+Z.card:=by exact_mod_cast hunion
    linarith [hupper.1,hupper.2]
  have hpos:(0:ℝ)≤Fintype.card Vkeep:=Nat.cast_nonneg _
  have hmul:=mul_le_mul_of_nonneg_right hξ hpos
  nlinarith [mul_nonneg he (sub_nonneg.mpr hhalf)]
end Oberwolfach
