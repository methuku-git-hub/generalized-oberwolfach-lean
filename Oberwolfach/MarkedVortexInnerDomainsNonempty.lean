module

public import Oberwolfach.MarkedVortexParentHubSizes

@[expose] public section
/-! Nonemptiness of both domains at every inner vortex level, including the
last nonempty level; the indices use the original rounded index sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_domains_nonempty
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hb:0≤β) (hb1:β≤1/4)
    (he:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length):
    0<Fintype.card (markedVortexVertexType Q (i+1)) ∧
      0<Fintype.card (markedVortexHubType Q (i+1)):=by
  have hvBound:(Q.vertices Q.length).card≤(Q.vertices (i+1)).card:=by
    have hsub:=Q.extendedVertices_subset (show i+1≤Q.length by omega)
    rw [Q.extendedVertices_eq (by omega:i+1≤Q.length),Q.extendedVertices_eq (le_refl _)] at hsub
    exact Finset.card_le_card hsub
  have hvPos:0<(Q.vertices (i+1)).card:=by
    have hmR:0<(m:ℝ):=by exact_mod_cast hm
    have hpos:0<ε*(m:ℝ)/2:=by positivity
    have hcard:((Q.vertices Q.length).card:ℝ)≤(Q.vertices (i+1)).card:=by exact_mod_cast hvBound
    have hh:0<((Q.vertices (i+1)).card:ℝ):=hpos.trans_le (Q.terminal_lower.trans hcard)
    exact_mod_cast hh
  have hHub:=Q.index_size_lower hreg hn hD hρ hρlo hb hb1 (i:=i+1) (by omega)
  have huPos:0<(Q.indices (i+1)).card:=by
    have hvR:0<((Q.vertices (i+1)).card:ℝ):=by exact_mod_cast hvPos
    have hh:0<((Q.indices (i+1)).card:ℝ):=(by positivity : 0<ρ₀/8*((Q.vertices (i+1)).card:ℝ)).trans_le hHub
    exact_mod_cast hh
  constructor
  · change 0<Fintype.card ↥(Q.extendedVertices (i+1))
    rw [Fintype.card_coe,Q.extendedVertices_eq (by omega:i+1≤Q.length)]
    exact hvPos
  · change 0<Fintype.card ↥(Q.extendedIndices (i+1))
    rw [Fintype.card_coe,Q.extendedIndices_eq (by omega:i+1≤Q.length)]
    exact huPos
end Oberwolfach
