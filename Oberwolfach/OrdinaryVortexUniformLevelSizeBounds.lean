module

public import Oberwolfach.OrdinaryUnifiedVortexSizeChoice
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The terminal-size choice supplies every parent and inner level of the
actual vortex with the same previously fixed cardinality threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_uniform_level_size_bounds
    {n q D mv N:ℕ} {β ε:ℝ} (P:SimpleGraph (Fin n)) (Q:Vortex (Fin q) P D β ε mv)
    (hN:(N:ℝ)≤ε*mv/2):
    (∀i,i≤Q.length→N≤(Q.extendedVertices i).card) ∧
    (∀i,i<Q.length→N≤(markedVortexInnerVertices Q i).card) :=by
  have hlevels:∀i,i≤Q.length→N≤(Q.extendedVertices i).card:=by
    intro i hi
    have hh:=Q.vertices_lower hi
    rw [←Q.extendedVertices_eq hi] at hh
    exact_mod_cast hN.trans hh
  refine ⟨hlevels,?_⟩
  intro i hi
  obtain ⟨hx,_,_,_⟩:=marked_vortex_inner_images Q i
  have hdec:(fun (x y:Fin n)=>Classical.propDecidable (x=y))=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hdec] at hx
  change (markedVortexInnerVertices Q i).image (Subtype.val:markedVortexVertexType Q i→Fin n)=Q.extendedVertices (i+1) at hx
  have hc: (markedVortexInnerVertices Q i).card=(Q.extendedVertices (i+1)).card:=by
    rw [←hx,Finset.card_image_of_injective _ Subtype.val_injective]
  rw [hc]
  exact hlevels (i+1) (by omega)
end Oberwolfach
