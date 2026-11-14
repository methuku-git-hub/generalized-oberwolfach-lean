module

public import Oberwolfach.OrdinaryRootCoverNonrootData
public import Oberwolfach.ResourceDecompositions

@[expose] public section
/-! Outside the good first-stage event, empty root sets admit the empty
cover. This supports total outcome-dependent selections without assumptions
on bad outcomes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_empty_root_cover (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (r:ℕ) (η ell:ℝ) (hη:0≤η) (hell:0≤ell):
    Nonempty (OrdinaryRootCoverNonrootData Q F H X ∅ Z ∅ r η ell):=by
  have hres:ordinaryHostResources (⊥:SimpleGraph V) (fun (_:V) (_:U)=>False)=∅:=by
    ext e
    cases e with
    | inl e=>simp [ordinaryHostResources_rim]
    | inr e=>rcases e with ⟨v,u⟩;simp [ordinaryHostResources_spoke]
  have hp:ordinaryPhysicalGraph (⊥:SimpleGraph V) (fun (_:V) (_:U)=>False)=⊥:=by
    ext a b
    cases a <;> cases b <;> simp [ordinaryPhysicalGraph]
  have hi:spanningRestriction (ordinaryPhysicalGraph (⊥:SimpleGraph V) (fun (_:V) (_:U)=>False))
      (ordinaryInnerVertices X Z)=⊥:=by
    rw [hp]
    ext a b
    simp [spanningRestriction_adj]
  have hhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (⊥:SimpleGraph V) (fun (_:V) (_:U)=>False)):=by
    rw [hres]
    exact resource_decomposition_empty _
  have hdec:HasOrdinaryWheelDecomposition (⊥:SimpleGraph V) (fun (_:V) (_:U)=>False) r:=by
    unfold HasOrdinaryWheelDecomposition
    rw [hres]
    exact resource_decomposition_empty _
  refine ⟨{ toOrdinaryRootCoverData := {
    rim:=⊥,spokes:=fun _ _=>False,rim_sub:=bot_le,spoke_sub:=by simp,
    host_decomposition:=hhost,decomposition:=hdec,inner_degree:=?_,outside_degree:=?_,
    avoids_deep:=?_,covers_rim:=?_,covers_row:=?_,covers_column:=?_ }, nonroot_degree:=?_ }⟩
  · intro a
    rw [hi]
    simpa using hη
  · intro a ha
    rw [hp]
    simpa using hell
  · rw [hp]
    apply disjoint_iff_inf_le.mpr
    simp
  · intro v hv
    simpa using hv
  · intro v hv
    simpa using hv
  · intro u hu
    simpa using hu
  · intro a ha
    rw [hp]
    simpa using hell
end Oberwolfach
