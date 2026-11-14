module

public import Oberwolfach.OrdinaryInitialSharpReferenceScaledProfileAt
public import Oberwolfach.OrdinaryVortexTriangleInnerSizeAndIndices

@[expose] public section
/-! The actual corrected initial host and its inner-scaled edit bound give
the full-parent subgraph and ambient-rate inputs of the triangle factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)

theorem ordinary_triangle_initial_corrected_parent_bridge
    (G F:SimpleGraph V) (hG:G≤P) (hGF:Disjoint G F)
    (L ζ rateParent:ℝ) (hζ:0≤ζ) (hζrate:ζ≤rateParent)
    (hL:L≤ζ*(markedVortexInnerVertices Q 0).card):
    let f:=markedVortexVertexEmbedding Q 0;
    (G.comap f)≤(P.comap f)\(F.comap f) ∧
    L≤rateParent*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0):=by
  intro f
  constructor
  · intro v w h
    exact ⟨hG h,fun hf=>(disjoint_iff_inf_le.mp hGF) ⟨h,hf⟩⟩
  · have hi:(markedVortexInnerVertices Q 0).card≤Fintype.card (markedVortexVertexType Q 0):=Finset.card_le_univ _
    have hn:Fintype.card (markedVortexVertexType Q 0)≤
        Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0):=
      Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    have hr:0≤rateParent:=hζ.trans hζrate
    have h1:=mul_le_mul_of_nonneg_right hζrate (show (0:ℝ)≤(markedVortexInnerVertices Q 0).card by positivity)
    have h2:=mul_le_mul_of_nonneg_left (show ((markedVortexInnerVertices Q 0).card:ℝ)≤
      Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0) by exact_mod_cast hi.trans hn) hr
    exact hL.trans (h1.trans h2)
end Oberwolfach
