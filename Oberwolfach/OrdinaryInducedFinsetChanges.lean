module

public import Oberwolfach.OrdinaryInducedFinsetTransfer

@[expose] public section
/-! Symmetric changes commute with passing to a fixed induced domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_induced_finset_filter (T A:Finset V) (p:V→Prop):
    ordinaryInducedFinset T (A.filter p)=(ordinaryInducedFinset T A).filter (fun v=>p v.val):=by
  ext v
  simp [ordinaryInducedFinset]

theorem ordinary_induced_finset_changed (T A B:Finset V):
    ordinaryInducedFinset T (changed A B)=changed (ordinaryInducedFinset T A) (ordinaryInducedFinset T B):=by
  ext v
  simp [ordinaryInducedFinset,changed]

theorem ordinary_induced_finset_changed_card (T A B:Finset V) (hA:A⊆T) (hB:B⊆T):
    (changed (ordinaryInducedFinset T A) (ordinaryInducedFinset T B)).card=(changed A B).card:=by
  rw [←ordinary_induced_finset_changed]
  apply ordinary_induced_finset_card
  intro x hx
  simp only [changed,Finset.mem_union,Finset.mem_sdiff] at hx
  exact hx.elim (fun h=>hA h.1) (fun h=>hB h.1)
end Oberwolfach
