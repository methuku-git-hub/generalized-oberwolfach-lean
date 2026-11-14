module

public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! The final nonempty vertex and hub pair has bounded total size, so an
absorber capacity can be selected after the terminal vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_terminal_pair_capacity
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (L:ℕ) (hL:L+1=Q.length):
    (markedVortexInnerVertices Q L).card+(markedVortexInnerHubs Q L).card≤2*m := by
  obtain ⟨hI,_,hJ,_⟩:=marked_vortex_inner_cardinalities Q L
  rw [hL,Q.extendedVertices_eq (le_refl Q.length)] at hI
  rw [hL,Q.extendedIndices_eq (le_refl Q.length)] at hJ
  have hdouble:=Q.index_size_upper hreg hn hD he hρhi (le_refl Q.length)
  have hJlo: (Q.indices Q.length).card≤(Q.vertices Q.length).card:=by omega
  have hterm: (Q.vertices Q.length).card<m:=Q.terminal_upper
  omega

theorem marked_vortex_terminal_pair_image_capacity
    {V₀ U₀:Type} [DecidableEq V₀] [DecidableEq U₀]
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (L:ℕ) (hL:L+1=Q.length)
    (f:markedVortexVertexType Q L↪V₀) (g:markedVortexHubType Q L↪U₀):
    ((markedVortexInnerVertices Q L).image f).card+
      ((markedVortexInnerHubs Q L).image g).card≤2*m := by
  rw [Finset.card_image_of_injective _ f.injective,Finset.card_image_of_injective _ g.injective]
  exact marked_vortex_terminal_pair_capacity Q hreg hn hD hρhi he L hL
end Oberwolfach
