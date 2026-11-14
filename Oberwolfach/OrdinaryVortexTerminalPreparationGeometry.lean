module

public import Oberwolfach.MarkedVortexTerminalDecompositionGeometry

@[expose] public section
/-! The actual vortex terminal sets fit the absorber and lie in its
first protected domain whenever its support budget covers the terminal size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_terminal_preparation_geometry
    {n q D mv mAbs:ℕ} (P:SimpleGraph (Fin n)) (β ε:ℝ)
    (Q:Vortex (Fin q) P D β ε mv) (hn:0<n) (hreg:P.IsRegularOfDegree D) (hD:0<D)
    (hρhi:initialIndexDensity (Fin q) D≤1) (hε:0≤ε) (hAbs:2*mv≤mAbs):
    (Q.extendedVertices Q.length).card+(Q.extendedIndices Q.length).card≤mAbs ∧
    Q.extendedVertices Q.length⊆Q.extendedVertices 1 ∧ Q.extendedIndices Q.length⊆Q.extendedIndices 1 :=by
  letI:Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hlen:Q.length-1+1=Q.length:=by have hh:=Q.length_pos;omega
  have hgeo:=marked_vortex_terminal_decomposition_geometry P D mv β ε ε Q (Q.length-1) mAbs 0 hlen
    hreg (by simpa using hn) hD hρhi hε (le_refl ε) hAbs
  refine ⟨?_,?_,?_⟩
  · simpa only [hlen] using hgeo.1
  · exact Q.extendedVertices_subset (by have hh:=Q.length_pos;omega)
  · exact Q.extendedIndices_subset (by have hh:=Q.length_pos;omega)
end Oberwolfach
