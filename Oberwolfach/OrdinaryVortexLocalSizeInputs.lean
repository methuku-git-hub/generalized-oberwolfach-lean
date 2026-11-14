module

public import Oberwolfach.OrdinaryVortexBoundaryIndexBounds
public import Oberwolfach.OrdinaryVortexInnerCardinalBounds
public import Oberwolfach.VortexLocalRowSizeConditions

@[expose] public section
/-! A single sufficiently large terminal vortex size supplies all of the
local cardinality inputs used by the asymmetric pairing event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D mv:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε mv)

theorem ordinary_vortex_local_size_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (Ncert N:ℕ) (hN:Ncert≤N) (hsize:2/ε≤N) (hterminal:(N:ℝ)≤ε*mv/2):
    let A:=markedVortexInnerVertices Q i;let Z:=markedVortexInnerHubs Q i;
    A.Nonempty ∧ Ncert≤A.card ∧ (ρ₀/8)*(A.card:ℝ)≤Z.card ∧ Z.card≤A.card ∧
    Fintype.card {u:markedVortexHubType Q i // u∉Z}≤A.card^2 ∧
    Fintype.card {v:markedVortexVertexType Q i // v∉A}≤(ordinaryPhysicalInnerDomain A Z).card^2:=by
  intro A Z
  have hcard:N≤A.card:=by
    have hh:=Q.extended_card_at_least_threshold hterminal (by omega : i+1≤Q.length)
    have heq:=(marked_vortex_inner_cardinalities Q i).1
    exact heq.symm ▸ hh
  have hsmall:2/ε≤(A.card:ℝ):=hsize.trans (by exact_mod_cast hcard)
  have hinner:=ordinary_vortex_inner_cardinal_bounds Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi hsmall
  have hboundary:=ordinary_vortex_boundary_index_bounds Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi hsmall
  exact ⟨hinner.1,hN.trans hcard,hinner.2.1,hinner.2.2,hboundary.1,hboundary.2⟩
end Oberwolfach
