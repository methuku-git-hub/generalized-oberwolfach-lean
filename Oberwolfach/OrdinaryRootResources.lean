module

public import Oberwolfach.OrdinaryResourceEndpointSets

@[expose] public section

/-! Exclude every resource supported on the chosen row and hub roots.
This changes neither the host nor any supplied cycle coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRootResources (R:Finset V) (B:Finset U) : Finset (Sym2 V⊕(V×U)) :=
  Finset.univ.filter (fun e=>ordinaryResourceRows {e}⊆R ∧ ordinaryResourceHubs {e}⊆B)

theorem ordinaryRootResources_rows (R:Finset V) (B:Finset U) :
    ordinaryResourceRows (ordinaryRootResources R B)⊆R := by
  intro v hv
  obtain ⟨e,he,hv⟩:=Finset.mem_biUnion.mp hv
  exact (Finset.mem_filter.mp he).2.1 (Finset.mem_biUnion.mpr ⟨e,by simp,hv⟩)

theorem ordinaryRootResources_hubs (R:Finset V) (B:Finset U) :
    ordinaryResourceHubs (ordinaryRootResources R B)⊆B := by
  intro v hv
  obtain ⟨e,he,hv⟩:=Finset.mem_biUnion.mp hv
  exact (Finset.mem_filter.mp he).2.2 (Finset.mem_biUnion.mpr ⟨e,by simp,hv⟩)

theorem ordinaryRootResources_contains (L:Finset (Sym2 V⊕(V×U))) (R:Finset V) (B:Finset U)
    (hr:ordinaryResourceRows L⊆R) (hb:ordinaryResourceHubs L⊆B) : L⊆ordinaryRootResources R B := by
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (ordinaryResourceRows_mono (Finset.singleton_subset_iff.mpr he)).trans hr,
    (ordinaryResourceHubs_mono (Finset.singleton_subset_iff.mpr he)).trans hb⟩

theorem ordinaryRootResources_rim (R:Finset V) (B:Finset U) (v w:V)
    (hv:v∈R) (hw:w∈R) : Sum.inl s(v,w)∈ordinaryRootResources R B := by
  simp [ordinaryRootResources,ordinaryResourceRows,ordinaryResourceHubs,Sym2.toFinset_mk_eq,Finset.insert_subset_iff,Finset.singleton_subset_iff,hv,hw]

theorem ordinaryRootResources_spoke (R:Finset V) (B:Finset U) (v:V) (u:U)
    (hv:v∈R) (hu:u∈B) : Sum.inr (v,u)∈ordinaryRootResources R B := by
  simp [ordinaryRootResources,ordinaryResourceRows,ordinaryResourceHubs,hv,hu]

theorem ordinaryRootResources_avoid (K:Finset (Sym2 V⊕(V×U))) (R:Finset V) (B:Finset U)
    (h:Disjoint K (ordinaryRootResources R B)) :
    (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉K)∧(∀ v∈R,∀ u∈B,Sum.inr (v,u)∉K) := by
  constructor
  · intro v hv w hw he
    exact Finset.disjoint_left.mp h he (ordinaryRootResources_rim R B v w hv hw)
  · intro v hv u hu he
    exact Finset.disjoint_left.mp h he (ordinaryRootResources_spoke R B v u hv hu)

theorem ordinaryRootResources_rim_iff (R:Finset V) (B:Finset U) (v w:V) :
    Sum.inl s(v,w)∈ordinaryRootResources R B↔v∈R∧w∈R := by
  simp [ordinaryRootResources,ordinaryResourceRows,ordinaryResourceHubs,Sym2.toFinset_mk_eq,Finset.insert_subset_iff,Finset.singleton_subset_iff]

theorem ordinaryRootResources_spoke_iff (R:Finset V) (B:Finset U) (v:V) (u:U) :
    Sum.inr (v,u)∈ordinaryRootResources R B↔v∈R∧u∈B := by
  simp [ordinaryRootResources,ordinaryResourceRows,ordinaryResourceHubs]

end Oberwolfach
