module

public import Oberwolfach.FirstVortexGlobalGeometryEventually
public import Oberwolfach.LongClassRequiredGlobalGeometry
public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
/-! After fixing the global load tolerance, choose the vortex scale and a
host threshold uniformly before the graph and the inner set are supplied. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_global_geometry_ordered_choice
    (d:ℕ) (δsmall cap:ℝ) (hδ:0<δsmall) (hcap:0<cap):
    ∃ε:ℝ,0<ε ∧ ε≤cap ∧ ε<δsmall/4 ∧ ∃N:ℕ,∀n:ℕ,N≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] (P S Sel Used:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n))),
    let I:=Q.extendedVertices 1
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    ((I.card:ℝ)≤ε*n) ∧ ∀v,((Kplus.degree v:ℝ)≤δsmall*n/4) :=by
  let ε:=min (cap/2) (δsmall/8)
  have hε:0<ε:=by dsimp [ε];positivity
  have hεcap:ε≤cap:=by dsimp [ε];have hh:=min_le_left (cap/2) (δsmall/8);linarith
  have hεgap:ε<δsmall/4:=by dsimp [ε];have hh:=min_le_right (cap/2) (δsmall/8);linarith
  obtain ⟨N,hN⟩:=first_vortex_global_geometry_eventually d ε δsmall hεgap
  refine ⟨ε,hε,hεcap,hεgap,N,?_⟩
  intro n hn U _ _ P S Sel Used D m β Q π Req Pack I K Kplus
  have hI:((I.card:ℝ)≤ε*n):=by simpa only [I,Fintype.card_fin] using Q.first_inner_vertex_size_upper hε.le
  refine ⟨hI,?_⟩
  intro v
  have hg:=long_class_required_global_geometry S Sel Used π d I Req Pack v
  have hr:((Kplus.degree v:ℝ)≤(I.card:ℝ)+((6*d+2:ℕ):ℝ)):=by exact_mod_cast hg
  linarith [hN n hn]
end Oberwolfach
