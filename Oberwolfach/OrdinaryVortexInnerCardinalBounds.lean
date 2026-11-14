module

public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Local vertex and hub cardinalities at a fixed vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem ordinary_vortex_inner_cardinal_bounds
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length)
    (hsize:2/ε≤((markedVortexInnerVertices Q i).card:ℝ)):
    (markedVortexInnerVertices Q i).Nonempty ∧
    (ρ₀/8)*((markedVortexInnerVertices Q i).card:ℝ)≤(markedVortexInnerHubs Q i).card ∧
    (markedVortexInnerHubs Q i).card≤(markedVortexInnerVertices Q i).card:=by
  have hf:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
  have hDp:0<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith)
  have hu:=Q.index_size_upper hreg hn hDp hε.le hρhi (by omega : i+1≤Q.length)
  obtain ⟨hI,_,hJ,_⟩:=marked_vortex_inner_cardinalities Q i
  rw [Q.extendedVertices_eq (by omega : i+1≤Q.length)] at hI
  rw [Q.extendedIndices_eq (by omega : i+1≤Q.length)] at hJ
  have hne:(markedVortexInnerVertices Q i).Nonempty:=by
    apply Finset.card_pos.mp
    have hp:0<2/ε:=by positivity
    have hp':(0:ℝ)<(markedVortexInnerVertices Q i).card:=lt_of_lt_of_le hp hsize
    exact_mod_cast hp'
  refine ⟨hne,hf.2.1,?_⟩
  rw [hI,hJ]
  omega
end Oberwolfach
