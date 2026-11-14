module

public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The pre-exposure active-size margins imply the minimum finite-domain
sizes required by the joint reference event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_event_minimum_domains (M i:ℕ) (he:0≤ε)
    (hI:(M:ℝ)≤(1-ε)*((markedVortexInnerVertices Q i).card:ℝ))
    (hJ:(M:ℝ)≤(1-ε)*((markedVortexInnerHubs Q i).card:ℝ)):
    M≤(markedVortexInnerVertices Q i).card ∧ M≤(markedVortexInnerHubs Q i).card ∧
    M≤Fintype.card (markedVortexVertexType Q i) ∧ M≤Fintype.card (markedVortexHubType Q i):=by
  have hIc:0≤((markedVortexInnerVertices Q i).card:ℝ):=Nat.cast_nonneg _
  have hJc:0≤((markedVortexInnerHubs Q i).card:ℝ):=Nat.cast_nonneg _
  have hIr:(M:ℝ)≤(markedVortexInnerVertices Q i).card:=by nlinarith [mul_nonneg he hIc]
  have hJr:(M:ℝ)≤(markedVortexInnerHubs Q i).card:=by nlinarith [mul_nonneg he hJc]
  have hIn:M≤(markedVortexInnerVertices Q i).card:=by exact_mod_cast hIr
  have hJn:M≤(markedVortexInnerHubs Q i).card:=by exact_mod_cast hJr
  exact ⟨hIn,hJn,hIn.trans (Finset.card_le_univ _),hJn.trans (Finset.card_le_univ _)⟩
end Oberwolfach
