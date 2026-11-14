module

public import Oberwolfach.MarkedSpokeLoadGrouping

@[expose] public section

/-! Restrict the residual spoke load to hubs incident with an original
spoke. The number of switches is bounded by the original number of spokes,
not by the order of the host hub class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U S:Type} [Fintype S] [Fintype U] [DecidableEq S] [DecidableEq V] [DecidableEq U]

 theorem marked_active_hub_card (hub:S→U):Fintype.card {u:U // ∃ s:S,hub s=u}≤Fintype.card S:=by
  let f:S→{u:U // ∃ s:S,hub s=u}:=fun s=>⟨hub s,s,rfl⟩
  have hf:Function.Surjective f:=by
    intro u
    obtain ⟨s,hs⟩:=u.property
    exact ⟨s,Subtype.ext hs⟩
  exact Fintype.card_le_of_surjective f hf

 theorem spokePathHubVertices_empty (m:ℕ) (p:S→(Fin m↪V)) (hub:S→U) (u:U)
    (hu:¬∃ s:S,hub s=u):spokePathHubVertices m p hub u=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨s,_,_⟩:=Finset.mem_biUnion.mp hv
  exact hu ⟨s.val,s.property⟩

 theorem marked_spoke_path_active_load (m:ℕ) (p:S→(Fin m↪V)) (hub:S→U) (ψ:U→U)
    (e:Finset V⊕(V×U)):
    (∑ u:U,((if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,u)) then (1:ℤ) else 0)-
      (if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)))=
    ∑ u:{u:U // ∃ s:S,hub s=u},
      ((if e∈(spokePathHubVertices m p hub u.val).image (fun v=>Sum.inr (v,u.val)) then (1:ℤ) else 0)-
        (if e∈(spokePathHubVertices m p hub u.val).image (fun v=>Sum.inr (v,ψ u.val)) then 1 else 0)):=by
  let f:U→ℤ:=fun u=>
    (if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,u)) then 1 else 0)-
      (if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)
  have hz:(∑ u:{u:U // ¬∃ s:S,hub s=u},f u.val)=0:=by
    apply Finset.sum_eq_zero
    intro u _
    simp only [f,spokePathHubVertices_empty m p hub u.val u.property,Finset.image_empty,
      Finset.notMem_empty,ite_false,sub_self]
  have hh:=Fintype.sum_subtype_add_sum_subtype (fun u=>∃ s:S,hub s=u) f
  rw [hz,add_zero] at hh
  exact hh.symm

end Oberwolfach
