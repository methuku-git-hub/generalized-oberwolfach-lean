module

public import Oberwolfach.MarkedPackingHubFactors
public import Oberwolfach.MarkedHubFactorVertexCount

@[expose] public section
/-! The prescribed spoke set at each hub has (m+1) vertices for each
marked root in a physical marked-wheel decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_packing_hub_vertex_count
    {V U E K:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}
    (P:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (hP:∀W∈P,∀Z∈P,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hspoke:∀v u,Sum.inr (v,u)∈P.biUnion markedWheelPhysicalResources ↔ H₀ v u∨Hₖ v u)
    (Y:U→Finset V) (hmarked:∀u x,Hₖ x u↔x∈Y u) (hsep:∀u x,Hₖ x u→¬H₀ x u):
    ∀u,(Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)).card=(m+1)*(Y u).card := by
  intro u
  obtain ⟨M,hM,hcover,_⟩:=marked_packing_to_hub_factors P hP hspoke u
  have hYS:Y u⊆Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u):=by
    intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inr ((hmarked u x).2 hx)
  exact marked_hub_factor_vertex_count tail head ktail khead m b π H₀ Hₖ u M hM _ (Y u) hcover hYS (hmarked u) (hsep u)
end Oberwolfach
