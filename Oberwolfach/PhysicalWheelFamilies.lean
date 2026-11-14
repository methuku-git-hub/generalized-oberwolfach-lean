module

public import Oberwolfach.PhysicalTriangleWheels
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Exact physical graphs of wheel families. Rim edges and spokes retain
their distinct coordinates under unions and graph disjointness. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U]

theorem wheelFamily_physical_graph {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}
    (W:I→OrdinaryWheel Q F H r):
    ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W)=
      ⨆ i,ordinaryWheelPhysicalGraph (W i):=by
  ext a b
  cases a <;> cases b <;>
    simp [ordinaryPhysicalGraph,ordinaryWheelPhysicalGraph,wheelFamilyRim,wheelFamilySpokes,eq_comm]

theorem ordinaryPhysicalGraph_sup (Q R:SimpleGraph V) (H K:V→U→Prop):
    ordinaryPhysicalGraph (Q⊔R) (fun a u=>H a u∨K a u)=
      ordinaryPhysicalGraph Q H⊔ordinaryPhysicalGraph R K:=by
  ext a b
  cases a <;> cases b <;> simp [ordinaryPhysicalGraph,SimpleGraph.sup_adj]

theorem ordinaryPhysicalGraph_disjoint (Q R:SimpleGraph V) (H K:V→U→Prop):
    Disjoint (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph R K)↔
      Disjoint Q R ∧ ∀ a u,¬(H a u∧K a u):=by
  constructor
  · intro h
    refine ⟨disjoint_iff_inf_le.mpr (fun a b hab=>?_),fun a u hau=>?_⟩
    · exact (disjoint_iff_inf_le.mp h) (v:=Sum.inl a) (w:=Sum.inl b) hab
    · exact (disjoint_iff_inf_le.mp h) (v:=Sum.inl a) (w:=Sum.inr u) hau
  · rintro ⟨hQ,hH⟩
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    cases a with
    | inl a=>
      cases b with
      | inl b=>exact disjoint_iff_inf_le.mp hQ hab
      | inr b=>exact (hH a b hab).elim
    | inr a=>
      cases b with
      | inl b=>exact (hH b a hab).elim
      | inr b=>exact hab.1

theorem graph_map_inl_physical (Q:SimpleGraph V):
    Q.map (Function.Embedding.inl:V↪V⊕U)=ordinaryPhysicalGraph Q (fun _ _=>False):=by
  ext a b
  cases a <;> cases b <;> simp [SimpleGraph.map_adj,ordinaryPhysicalGraph]

end Oberwolfach
