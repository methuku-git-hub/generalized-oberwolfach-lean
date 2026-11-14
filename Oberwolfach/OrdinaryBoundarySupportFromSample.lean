module

public import Oberwolfach.OrdinaryBoundarySupportGeometry
public import Oberwolfach.BoundaryReserveSupportAfterPacking

@[expose] public section
/-! The selection support bounds hold for the actual ordinary boundary
classes when they lie in the surviving physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_boundary_supports_from_sample (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (G C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (τ ε L ρ:ℝ)
    (hτ:0≤τ) (hgood:BoundaryReserveSupportGood G τ ε σ)
    (hCR:Disjoint C (retainedGraph G σ))
    (hL:∀w,(((G\retainedGraph G σ)\C).degree w:ℝ)+(D.degree w:ℝ)≤L)
    (hbound:ordinaryBoundaryGraph Q H X Z≤(G\C)\D)
    (hdeg:(τ+ε)*Fintype.card (V⊕U)+L≤ρ*Fintype.card (V⊕U))
    (hpair:(τ^2+ε)*Fintype.card (V⊕U)+2*L≤ρ^2*Fintype.card (V⊕U)):
    let S:=ordinaryBoundaryPhysicalSupports Q H X Z;
    (∀i j,i≠j→((S i∩S j).card:ℝ)≤ρ^2*Fintype.card (V⊕U)) ∧
    (∀w,((Finset.univ.filter (fun i=>w∈S i)).card:ℝ)≤ρ*Fintype.card (V⊕U)):=by
  intro S
  have hS:∀i,S i⊆(((G\C)\D).neighborFinset (ordinaryBoundaryPhysicalRoot X Z i)):=by
    intro i w hw
    have hh:=ordinary_boundary_physical_supports_neighbor Q H X Z i hw
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    exact hbound ((SimpleGraph.mem_neighborFinset _ _ _).mp hh)
  exact boundary_support_after_packing G C D σ τ ε L ρ hτ hgood hCR hL
    (ordinaryBoundaryPhysicalRoot X Z) S hS hdeg hpair
end Oberwolfach
