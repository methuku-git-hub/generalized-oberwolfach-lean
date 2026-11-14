module

public import Oberwolfach.OrdinaryPackingCleanupData

@[expose] public section
/-! The physical graph of an ordinary wheel packing is contained in the
physical graph of its host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_packing_physical_subhost (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (M:Finset (OrdinaryWheel Q F H r)):
    ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)≤ordinaryPhysicalGraph Q H:=by
  have hr:=ordinaryWheelRimGraph_subhost M
  have hs:∀v u,ordinaryPackingSpokes M v u→H v u:=by
    intro v u hvu
    obtain ⟨W,hW,hu,hv⟩:=hvu
    rw [←hu]
    exact W.property.1 v hv
  intro a b hab
  cases a with
  | inl v=>cases b with
    | inl w=>exact hr hab
    | inr u=>exact hs v u hab
  | inr u=>cases b with
    | inl v=>exact hs v u hab
    | inr z=>exact hab.elim
end Oberwolfach
