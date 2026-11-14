module

public import Oberwolfach.FirstVortexGeometricActiveCeiling
public import Oberwolfach.MarkedVortexPhysicalSpokeLossBudget

@[expose] public section
/-! Apply the geometric required-edge count to the actual first-inner spoke
loss bound, independently of the coarse assignment allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_geometric_physical_spoke_loss_eventually
    (d:ℕ) (ρ ε cap:ℝ) (hd:1≤d) (hρ:0<ρ) (hε:0<ε) (hcap:0<cap)
    (hrate:8*((1/2:ℝ)*ε^2)/((ρ/4)/40000)<cap*ε/128):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
      (P S Sel Used:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m)
      (Req:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n)))
      (hSP:S≤P) (hm:0<m) (hI:((Q.extendedVertices 1).card:ℝ)≤ε*n)
      (H H':Bool→Fin n→U→Prop) (ζ Pbound:ℝ)
      (hζ:ζ≤cap/128) (hP:Pbound≤cap*(ε*n)/128),
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K (Q.extendedVertices 1) Pack
      let L:ℝ:=⌈4*(Kplus.edgeFinset.card:ℝ)/(((ρ/4)/40000)*n)⌉₊;
      (∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
        ζ*(Q.extendedVertices 1).card+Pbound+2*L) →
      ∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
        cap*((markedVortexInnerVertices Q 0).card:ℝ) :=by
  obtain ⟨N,hN⟩:=first_vortex_geometric_active_ceiling_eventually d ρ ε cap hd hρ hε hcap hrate
  refine ⟨N,?_⟩
  intro n hn U _ _ P S Sel Used π D m β Q Req Pack hSP hm hI H H' ζ Pbound hζ hP K Kplus L hloss
  have hL:2*L≤cap*(ε*n)/128:=hN n hn P S Sel Used π (Q.extendedVertices 1) Req Pack hSP hI
  have hP':Pbound≤cap*(ε*Fintype.card (Fin n))/128:=by simpa using hP
  have hL':2*L≤cap*(ε*Fintype.card (Fin n))/128:=by simpa using hL
  exact marked_vortex_physical_spoke_loss_budget P D m β ε Q hε hm H H' cap ζ Pbound L hcap.le hζ hP' hL' hloss
end Oberwolfach
