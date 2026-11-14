module

public import Oberwolfach.OrdinaryLocalRestriction

@[expose] public section
/-! Complete all edges incident with vertices outside a fixed local domain.
This leaves the graph on the domain unchanged and makes roots outside it
irrelevant to common-neighborhood counts inside the domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryLocalHostAugment (Q:SimpleGraph V) (T:Finset V):SimpleGraph V where
  Adj v w := Q.Adj v w ∨ (v≠w ∧ (v∉T ∨ w∉T))
  symm:=⟨by
    intro v w h
    rcases h with h|⟨hne,ho⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm,ho.elim Or.inr Or.inl⟩⟩
  loopless:=⟨by
    intro v h
    rcases h with h|⟨hne,_⟩
    · exact Q.loopless.irrefl v h
    · exact hne rfl⟩

theorem ordinary_local_host_le_augment (Q:SimpleGraph V) (T:Finset V):Q≤ordinaryLocalHostAugment Q T:=by
  intro v w h
  exact Or.inl h

theorem ordinary_local_host_augment_inside (Q:SimpleGraph V) (T:Finset V) (v w:V)
    (hv:v∈T) (hw:w∈T): (ordinaryLocalHostAugment Q T).Adj v w↔Q.Adj v w:=by
  simp [ordinaryLocalHostAugment,hv,hw]

theorem ordinary_local_host_augment_common (Q:SimpleGraph V) (T S:Finset V):
    common T S (fun v=>(ordinaryLocalHostAugment Q T).neighborFinset v)=
    common T (S∩T) (fun v=>Q.neighborFinset v):=by
  ext v
  simp only [common,Finset.mem_filter,SimpleGraph.mem_neighborFinset,Finset.mem_inter]
  constructor
  · rintro ⟨hv,h⟩
    refine ⟨hv,?_⟩
    intro x hx
    exact (ordinary_local_host_augment_inside Q T x v hx.2 hv).mp (h x hx.1)
  · rintro ⟨hv,h⟩
    refine ⟨hv,?_⟩
    intro x hx
    by_cases hxT:x∈T
    · exact (ordinary_local_host_augment_inside Q T x v hxT hv).mpr (h x ⟨hx,hxT⟩)
    · exact Or.inr ⟨fun h=>hxT (h ▸ hv),Or.inl hxT⟩
end Oberwolfach
