module

public import Oberwolfach.MarkedVortexActiveGeometryBounds
public import Oberwolfach.MarkedVortexActiveDomainEquivalences

@[expose] public section
/-! The actual active geometry in the nested types used for sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_nested_vortex_active_geometry
    (ρ₀:ℝ) (hρ₀:0<ρ₀) (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1) (hb:0≤β) (hb1:β≤1/4)
    (he:0≤ε) (he1:ε≤1/4) (i:ℕ) (hi:i≤Q.length):
    let W:=markedVortexVertexType Q i
    let Z:=markedVortexHubType Q i
    let A:Finset W:=Finset.univ\markedVortexInnerVertices Q i
    let B:Finset Z:=Finset.univ\markedVortexInnerHubs Q i
    let Wnext:=markedVortexVertexType Q (i+1)
    let Anext:Finset Wnext:=Finset.univ\markedVortexInnerVertices Q (i+1);
    ((3*ρ₀/32)*(A.card:ℝ)≤B.card) ∧
    ((B.card:ℝ)≤(2/3)*(A.card:ℝ)) ∧
    ((Anext.card:ℝ)≤(4*ε/3)*A.card) ∧
    ((3*ε*(m:ℝ)/8)≤A.card) ∧ ((9*ρ₀*ε*(m:ℝ)/256)≤B.card):=by
  intro W Z A B Wnext Anext
  let Aphys:=Q.extendedVertices i\Q.extendedVertices (i+1)
  let Bphys:=Q.extendedIndices i\Q.extendedIndices (i+1)
  let AphysNext:=Q.extendedVertices (i+1)\Q.extendedVertices (i+2)
  have hA:A.card=Aphys.card:=by
    have hh:=Fintype.card_congr (markedVortexActiveVertexEquiv Q i)
    change Fintype.card ↥A=Fintype.card ↥Aphys at hh
    simpa only [Fintype.card_coe] using hh
  have hB:B.card=Bphys.card:=by
    have hh:=Fintype.card_congr (markedVortexActiveHubEquiv Q i)
    change Fintype.card ↥B=Fintype.card ↥Bphys at hh
    simpa only [Fintype.card_coe] using hh
  have hAnext:Anext.card=AphysNext.card:=by
    have hh:=Fintype.card_congr (markedVortexActiveVertexEquiv Q (i+1))
    change Fintype.card ↥Anext=Fintype.card ↥AphysNext at hh
    simpa only [Fintype.card_coe] using hh
  have hg:=marked_vortex_active_geometry_bounds Q ρ₀ hρ₀ hreg hn hD hρlo hρhi hb hb1 he he1 i hi
  rw [hA,hB,hAnext]
  exact ⟨hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2.1,hg.2.2.2.2.2.2⟩
end Oberwolfach
