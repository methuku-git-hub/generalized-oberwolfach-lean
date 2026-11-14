module

public import Oberwolfach.LongClassRequiredEdgeGeometry
public import Oberwolfach.FirstVortexActiveCeilingEventually

@[expose] public section
/-! The first-active ceiling can be controlled using the actual repaired
required graph, with no dependence on the coarse assignment allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_geometric_active_ceiling_eventually
    (d:ℕ) (ρ ε cap:ℝ) (hd:1≤d) (hρ:0<ρ) (hε:0<ε) (hcap:0<cap)
    (hrate:8*((1/2:ℝ)*ε^2)/((ρ/4)/40000)<cap*ε/128):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(P S Sel Used:SimpleGraph (Fin n))
      (π:Equiv.Perm (Fin n)) (I:Finset (Fin n)) (Req:Fin n→Fin n→Prop)
      (Pack:Finset (Sym2 (Fin n))), S≤P → (I.card:ℝ)≤ε*n →
      let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
      2*(⌈4*(Kplus.edgeFinset.card:ℝ)/(((ρ/4)/40000)*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  have hr:8*((1/2:ℝ)*ε^2+0*ε)/((ρ/4)/40000)<cap*ε/128:=by simpa using hrate
  obtain ⟨N,hN⟩:=first_vortex_active_ceiling_eventually d ρ ε cap (1/2) 0 hρ hε hcap hr
  refine ⟨N,?_⟩
  intro n hn P S Sel Used π I Req Pack hSP hI K Kplus
  apply hN n hn Kplus.edgeFinset.card
  have hE:=long_class_required_edge_geometry P S Sel Used π d I Req Pack hSP
  simp only [Fintype.card_fin] at hE
  have hEreal:(2:ℝ)*Kplus.edgeFinset.card≤(I.card:ℝ)^2+(6*(d:ℝ)+2)*n:=by
    exact_mod_cast hE
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hI0:(0:ℝ)≤I.card:=Nat.cast_nonneg _
  have hd1:(1:ℝ)≤d:=by exact_mod_cast hd
  have hsq:(I.card:ℝ)^2≤(ε*(n:ℝ))^2:=by nlinarith
  nlinarith [mul_nonneg (show (0:ℝ)≤n by positivity) (show (0:ℝ)≤(d:ℝ) from Nat.cast_nonneg _)]
end Oberwolfach
