module

public import Oberwolfach.FirstVortexGlobalGeometryBeforeSpacing

@[expose] public section
/-! The global graph estimate holds for every sufficiently small positive
vortex scale, so that scale can also satisfy later matching requirements. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_flexible_global_geometry
    (δsmall ε:ℝ) (hε:0<ε) (hgap:ε<δsmall/4):
    ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] (P S Sel Used:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n))),
    let I:=Q.extendedVertices 1
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    ((I.card:ℝ)≤ε*n) ∧ ∀v,((Kplus.degree v:ℝ)≤δsmall*n/4) :=by
  intro d
  obtain ⟨N,hN⟩:=first_vortex_global_geometry_eventually d ε δsmall hgap
  refine ⟨N,?_⟩
  intro n hn U _ _ P S Sel Used D m β Q π Req Pack I K Kplus
  have hI:((I.card:ℝ)≤ε*n):=by simpa only [I,Fintype.card_fin] using Q.first_inner_vertex_size_upper hε.le
  refine ⟨hI,?_⟩
  intro v
  have hg:=long_class_required_global_geometry S Sel Used π d I Req Pack v
  have hr:((Kplus.degree v:ℝ)≤(I.card:ℝ)+((6*d+2:ℕ):ℝ)):=by exact_mod_cast hg
  linarith [hN n hn]
end Oberwolfach
