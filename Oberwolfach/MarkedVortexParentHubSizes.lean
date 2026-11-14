module

public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Parent hub density and size fields on all fixed vortex levels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_parent_hub_sizes
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (ω:ℝ) (hω:ω≤ρ₀/8)
    (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,Fintype.card (markedVortexHubType Q i)≤Fintype.card (markedVortexVertexType Q i) ∧
      ω*Fintype.card (markedVortexVertexType Q i)≤(Fintype.card (markedVortexHubType Q i):ℝ):=by
  intro i hi
  have hDpos:0<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith only [hn',hD])
  have hupper:=Q.index_size_upper hreg hn hDpos he.le hρhi (i:=i) (by omega)
  have hlower:=Q.index_size_lower hreg hn hD hρ hρlo hb hb1 (i:=i) (by omega)
  have hcardW:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    change Fintype.card ↥(Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq (by omega:i≤Q.length)]
  have hcardZ:Fintype.card (markedVortexHubType Q i)=(Q.indices i).card:=by
    change Fintype.card ↥(Q.extendedIndices i)=(Q.indices i).card
    rw [Fintype.card_coe,Q.extendedIndices_eq (by omega:i≤Q.length)]
  rw [hcardW,hcardZ]
  constructor
  · omega
  · exact (mul_le_mul_of_nonneg_right hω (Nat.cast_nonneg _)).trans hlower
end Oberwolfach
