module

public import Oberwolfach.OrdinaryVortexBufferedDomains
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! Two consecutive fixed-vortex size estimates give the ambient-to-target
ratios required for tests on the pair two levels down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_two_step_event_sizes
    (P:SimpleGraph V) (D m:ℕ) (β ε K:ℝ) (Q:Vortex U P D β ε m) (i M:ℕ)
    (hK:1≤K) (hε:0≤ε)
    (h0:(Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(markedVortexInnerVertices Q i).card ∧
      (Fintype.card (markedVortexHubType Q i):ℝ)≤K*(markedVortexInnerVertices Q i).card)
    (h1:(M:ℝ)≤(1-ε)*(markedVortexInnerVertices Q (i+1)).card ∧
      (M:ℝ)≤(1-ε)*(markedVortexInnerHubs Q (i+1)).card ∧
      (Fintype.card (markedVortexVertexType Q (i+1)):ℝ)≤K*(markedVortexInnerVertices Q (i+1)).card ∧
      (Fintype.card (markedVortexVertexType Q (i+1)):ℝ)≤K*(markedVortexInnerHubs Q (i+1)).card):
    let A:=ordinaryVortexBufferedVertices Q i 2;let B:=ordinaryVortexBufferedHubs Q i 2;
    M≤A.card ∧ M≤B.card ∧
    (Fintype.card (markedVortexVertexType Q i):ℝ)≤K^2*A.card ∧
    (Fintype.card (markedVortexHubType Q i):ℝ)≤K^2*A.card ∧
    (Fintype.card (markedVortexVertexType Q i):ℝ)≤K^2*B.card:=by
  intro A B
  have hA:A.card=(markedVortexInnerVertices Q (i+1)).card:=by
    have hx:=congrArg Finset.card (ordinary_vortex_buffered_images Q i 2).1
    rw [Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective] at hx
    have hy:=(marked_vortex_inner_cardinalities Q (i+1)).1
    simpa only [show i+1+1=i+2 by omega] using hx.trans hy.symm
  have hB:B.card=(markedVortexInnerHubs Q (i+1)).card:=by
    have hx:=congrArg Finset.card (ordinary_vortex_buffered_images Q i 2).2
    rw [Finset.card_image_of_injective _ (markedVortexHubEmbedding Q i).injective] at hx
    have hy:=(marked_vortex_inner_cardinalities Q (i+1)).2.2.1
    simpa only [show i+1+1=i+2 by omega] using hx.trans hy.symm
  have hparent:(markedVortexInnerVertices Q i).card=Fintype.card (markedVortexVertexType Q (i+1)):=by
    rw [(marked_vortex_inner_cardinalities Q i).1]
    simp only [markedVortexVertexType,Fintype.card_coe]
  have hmA:(M:ℝ)≤A.card:=by
    rw [hA]
    have hc:(0:ℝ)≤(markedVortexInnerVertices Q (i+1)).card:=by positivity
    nlinarith only [h1.1,mul_nonneg hε hc]
  have hmB:(M:ℝ)≤B.card:=by
    rw [hB]
    have hc:(0:ℝ)≤(markedVortexInnerHubs Q (i+1)).card:=by positivity
    nlinarith only [h1.2.1,mul_nonneg hε hc]
  refine ⟨by exact_mod_cast hmA,by exact_mod_cast hmB,?_,?_,?_⟩
  · have hh:=mul_le_mul_of_nonneg_left h1.2.2.1 (show 0≤K by linarith)
    rw [hparent] at h0
    rw [hA]
    nlinarith only [h0.1,hh]
  · have hh:=mul_le_mul_of_nonneg_left h1.2.2.1 (show 0≤K by linarith)
    rw [hparent] at h0
    rw [hA]
    nlinarith only [h0.2,hh]
  · have hh:=mul_le_mul_of_nonneg_left h1.2.2.2 (show 0≤K by linarith)
    rw [hparent] at h0
    rw [hB]
    nlinarith only [h0.1,hh]
end Oberwolfach
