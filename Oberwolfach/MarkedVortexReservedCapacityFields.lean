module

public import Oberwolfach.MarkedVortexTerminalCapacity
public import Oberwolfach.MarkedVortexInnerUpperSizeInputs

@[expose] public section
/-! The first inner pair is small enough to be avoided by the reserved
absorber, and the terminal pair fits the capacity fixed from the vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_reserved_capacity_fields
    {V₀ U₀:Type} [DecidableEq V₀] [DecidableEq U₀]
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (εAbs:ℝ) (heAbs:ε≤εAbs)
    (L:ℕ) (hL:L+1=Q.length)
    (f:markedVortexVertexType Q L↪V₀) (g:markedVortexHubType Q L↪U₀):
    ((markedVortexInnerVertices Q 0).card:ℝ)≤εAbs*Fintype.card (markedVortexVertexType Q 0) ∧
    ((markedVortexInnerHubs Q 0).card:ℝ)≤εAbs*Fintype.card (markedVortexVertexType Q 0) ∧
    ((markedVortexInnerVertices Q L).image f).card+
      ((markedVortexInnerHubs Q L).image g).card≤2*m := by
  have hlen:0<Q.length := by omega
  have hfirst:=marked_vortex_inner_upper_size_inputs Q hreg hn hD hρhi he εAbs heAbs 0 hlen 0 (by omega)
  exact ⟨hfirst.1,hfirst.2,marked_vortex_terminal_pair_image_capacity Q hreg hn hD hρhi he L hL f g⟩
end Oberwolfach
