module

public import Oberwolfach.FirstVortexRequiredDegreeLocalBound
public import Oberwolfach.LongRequiredPreciseFromCommonIncidence

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_required_degree_from_precise_common_bounds
    (ε δ θ lam:ℝ) (d:ℕ) (hε:0<ε) (hδ:0<δ)
    (hθ:θ≤δ/32) (hlam:lam≤δ*ε/32):
    ∃N:ℕ,∀n≥N,∀{U:Type} [Fintype U] {P P₀ Sel:SimpleGraph (Fin n)}
      {D m:ℕ} {β:ℝ} (Q:Vortex U P D β ε m) (π:Equiv.Perm (Fin n))
      (Rel Match:Fin n→Fin n→Prop),
      1≤(Q.extendedVertices 1).card→
      (∀v,((longRequiredPhysicalGraph P P₀ Sel π d (Q.extendedVertices 1) Rel Match).degree v:ℝ)≤
        2*θ*(Q.extendedVertices 1).card+(n:ℝ)^(3/4:ℝ)+lam*n+(6*d+2:ℕ))→
      ∀v,((longRequiredPhysicalGraph P P₀ Sel π d (Q.extendedVertices 1) Rel Match).degree v:ℝ)≤
        δ*(Q.extendedVertices 1).card/4:=by
  obtain ⟨N,hN⟩:=first_vortex_required_degree_local_bound ε δ θ lam d hε hδ hθ hlam
  refine ⟨N,?_⟩
  intro n hn U _ P P₀ Sel D m β Q π Rel Match hpos hprec v
  apply hN n hn Q hpos ?_ v
  intro x
  convert hprec x using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
