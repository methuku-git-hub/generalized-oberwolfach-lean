module

public import Oberwolfach.OrdinaryBoundaryIndexCountFromInnerSize
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The quadratic matching union bounds follow from the size fields of the
same fixed vortex once its next vertex level is sufficiently large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem ordinary_vortex_boundary_index_bounds
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length)
    (hsize:2/ε≤((markedVortexInnerVertices Q i).card:ℝ)):
    Fintype.card {u:markedVortexHubType Q i // u∉markedVortexInnerHubs Q i}≤
        (markedVortexInnerVertices Q i).card^2 ∧
    Fintype.card {v:markedVortexVertexType Q i // v∉markedVortexInnerVertices Q i}≤
        (ordinaryPhysicalInnerDomain (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i)).card^2:=by
  have hf:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
  have hV:(Fintype.card (markedVortexVertexType Q i):ℝ)≤
      (2/ε)*((markedVortexInnerVertices Q i).card:ℝ):=by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hε).2
    nlinarith only [hf.1]
  have hV':(Fintype.card (markedVortexVertexType Q i):ℝ)≤
      (2/ε)*((markedVortexInnerVertices Q i).card:ℝ):=hV
  have hU:(Fintype.card (markedVortexHubType Q i):ℝ)≤
      (2/ε)*((markedVortexInnerVertices Q i).card:ℝ):=
    (Nat.cast_le.mpr hf.2.2).trans hV'
  exact ordinary_boundary_index_count_from_inner_size _ _ (2/ε) hsize hV' hU
end Oberwolfach
