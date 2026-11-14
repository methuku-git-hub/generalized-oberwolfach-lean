module

public import Oberwolfach.MarkedVortexGeometricRecordEvent
public import Oberwolfach.MarkedVortexActiveHubCardinality

@[expose] public section
/-! Extract the initial and active degree and size inputs required by the
first step of the selected vortex chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_geometric_chain_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (α ρ₀ κ hcut ξ xiDeep ω x:ℝ) (N NI L:ℕ) (hN:1≤N)
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hcut ξ xiDeep ω x N NI L):
    (ε/4)*Fintype.card (markedVortexVertexType Q 0)≤((markedVortexInnerVertices Q 0).card:ℝ) ∧
    0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)) ∧
    (Fintype.card (markedVortexVertexType Q 0):ℝ)/2≤
      2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D ∧
    2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D≤
      2*Fintype.card (markedVortexVertexType Q 0) ∧
    (Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)):ℝ)/2≤
      2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D ∧
    2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D≤
      2*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)) :=by
  have h0:0≤L:=Nat.zero_le _
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hInner,_,_,_⟩:=hGeo.1 0 h0
  obtain ⟨_,_,hDlo,hDhi,_⟩:=hGeo.2.1 0 h0
  obtain ⟨_,hActiveN,_⟩:=hGeo.2.2.1 0 h0
  obtain ⟨hActiveLo,hActiveHi⟩:=hGeo.2.2.2 0 h0
  rw [marked_vortex_active_hub_cardinality Q 0] at hActiveLo hActiveHi
  have hPos:0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)):=by
    have hNactive:N≤Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)):=by
      simpa only [Nat.zero_add] using hActiveN
    omega
  exact ⟨hInner,hPos,hDlo,hDhi,hActiveLo,hActiveHi⟩
end Oberwolfach
