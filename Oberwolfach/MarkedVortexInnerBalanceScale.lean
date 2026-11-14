module

public import Oberwolfach.MarkedLevelFiniteBalanceBound
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Choose the balance errors after the vortex ratio, and convert an
ambient-scale balance bound into the inner-scale bound needed by a level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_inner_balance_error_choices
    (r:ℕ) (ε η cap₁ cap₂:ℝ) (hε:0<ε) (hη:0<η) (hc₁:0<cap₁) (hc₂:0<cap₂):
    ∃ εBal ζBal:ℝ,0<εBal ∧ 0<ζBal ∧ εBal≤cap₁ ∧ ζBal≤cap₂ ∧
      εBal+((r+4)+2:ℕ)*ζBal≤η*ε/2 := by
  let c:ℝ:=((r+4)+2:ℕ)
  have hc:0<c:=by dsimp [c];positivity
  let εBal:=min cap₁ (η*ε/8)
  let ζBal:=min cap₂ (η*ε/(8*c))
  have h1:0<εBal:=by dsimp [εBal];positivity
  have h2:0<ζBal:=by dsimp [ζBal];positivity
  have h3:εBal≤η*ε/8:=min_le_right _ _
  have h4:ζBal≤η*ε/(8*c):=min_le_right _ _
  refine ⟨εBal,ζBal,h1,h2,min_le_left _ _,min_le_left _ _,?_⟩
  have hh:c*ζBal≤η*ε/8:=by
    have ht:=mul_le_mul_of_nonneg_left h4 hc.le
    have heq:c*(η*ε/(8*c))=η*ε/8:=by field_simp
    linarith
  have hp:0≤η*ε:=mul_nonneg hη.le hε.le
  dsimp [c] at hh
  nlinarith

theorem marked_vortex_inner_balance_from_ambient
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (he:0<ε) (hm:0<m) (r d:ℕ) (η εBal ζBal:ℝ) (hη:0≤η)
    (hsmall:εBal+((r+4)+2:ℕ)*ζBal≤η*ε/2)
    (i:ℕ) (hi:i<Q.length)
    (σ:RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color)
    (H:Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
    (hbal:MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) d (r+4) (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i)
      ((εBal+((r+4)+2:ℕ)*ζBal)*Fintype.card (markedVortexVertexType Q i)) σ H):
    MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) d (r+4) (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i)
      (η*(markedVortexInnerVertices Q i).card) σ H := by
  have hparent:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi.le]
  have hinner:(markedVortexInnerVertices Q i).card=(Q.vertices (i+1)).card:=by
    rw [(marked_vortex_inner_cardinalities Q i).1,Q.extendedVertices_eq (by omega:i+1≤Q.length)]
  have hsize:(ε/2)*(Fintype.card (markedVortexVertexType Q i):ℝ)≤(markedVortexInnerVertices Q i).card:=by
    rw [hparent,hinner]
    have hh:=(Q.consecutive_size_bounds he hm hi).1
    nlinarith
  have hn:(0:ℝ)≤Fintype.card (markedVortexVertexType Q i):=by positivity
  have hb:=mul_le_mul_of_nonneg_right hsmall hn
  have hs:=mul_le_mul_of_nonneg_left hsize hη
  intro z j
  have hh:=hbal z j
  nlinarith
end Oberwolfach
