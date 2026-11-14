module

public import Oberwolfach.OrdinaryBoundaryPhysicalDeletion

@[expose] public section
/-! Candidate factor edges inside the protected pair avoid the approximate
packing and survive any later cleanup edge they do not use. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_graph_typed_deletion (Q D:SimpleGraph V) (H S:V→U→Prop):
    ordinaryPhysicalGraph (Q\D) (fun v u=>H v u∧¬S v u)=
      ordinaryPhysicalGraph Q H\ordinaryPhysicalGraph D S:=by
  ext a b
  cases a with
  | inl v => cases b <;> rfl
  | inr u =>
    cases b with
    | inl v => rfl
    | inr u' =>
      change False ↔ (False ∧ ¬False)
      simp

theorem ordinary_inner_factor_edges_survive_cleanup
    (Q₀ Q Q':SimpleGraph V) (H₀ H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D:SimpleGraph (V⊕U))
    (hbase:ordinaryPhysicalGraph Q H≤spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z))
    (hC:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)))
    (hpost:ordinaryPhysicalGraph Q' H'=(ordinaryPhysicalGraph Q₀ H₀\C)\D):
    ordinaryPhysicalGraph Q H\D≤ordinaryPhysicalGraph Q' H':=by
  intro a b hab
  rw [hpost]
  have hi:=hbase hab.1
  have hg:=((spanningRestriction_adj _ _ _ _).mp hi).1
  have hnC:¬C.Adj a b:=fun hc=>(disjoint_iff_inf_le.mp hC) (v:=a) (w:=b) ⟨hc,hi⟩
  exact ⟨⟨hg,hnC⟩,hab.2⟩

theorem ordinary_boundary_after_physical_packings
    (Q₀ Q':SimpleGraph V) (H₀ H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D:SimpleGraph (V⊕U))
    (hpost:ordinaryPhysicalGraph Q' H'=(ordinaryPhysicalGraph Q₀ H₀\C)\D):
    ordinaryBoundaryGraph Q' H' X Z=(ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D:=by
  ext a b
  rw [ordinaryBoundaryGraph_adj,SimpleGraph.sdiff_adj,SimpleGraph.sdiff_adj,ordinaryBoundaryGraph_adj]
  have hh:(ordinaryPhysicalGraph Q' H').Adj a b↔((ordinaryPhysicalGraph Q₀ H₀\C)\D).Adj a b:=by rw [hpost]
  rw [hh]
  simp only [SimpleGraph.sdiff_adj]
  tauto
end Oberwolfach
