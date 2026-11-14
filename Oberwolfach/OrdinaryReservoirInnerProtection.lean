module

public import Oberwolfach.OrdinaryRootResources

@[expose] public section
/-! If reservoir rows on the inner set are restricted to the terminal rows,
avoiding terminal-row/inner-hub resources protects the whole inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reservoir_protects_inner_pair
    (C:Finset (Sym2 V⊕(V×U))) (Wterm Inner:Finset V) (B:Finset U)
    (hrows:ordinaryResourceRows C⊆Wterm∪(Finset.univ\Inner))
    (havoid:Disjoint C (ordinaryRootResources Wterm B)):
    Disjoint C (ordinaryRootResources Inner B):=by
  apply Finset.disjoint_left.mpr
  intro e he hinner
  have hsing:{e}⊆C:=Finset.singleton_subset_iff.mpr he
  have hsingInner:{e}⊆ordinaryRootResources Inner B:=Finset.singleton_subset_iff.mpr hinner
  have hrow:ordinaryResourceRows {e}⊆Wterm:=by
    intro v hv
    have hvall:=hrows ((ordinaryResourceRows_mono hsing) hv)
    have hvin: v∈Inner:=(ordinaryRootResources_rows Inner B) ((ordinaryResourceRows_mono hsingInner) hv)
    rcases Finset.mem_union.mp hvall with hvterm|hvout
    · exact hvterm
    · exact False.elim ((Finset.mem_sdiff.mp hvout).2 hvin)
  have hhub:ordinaryResourceHubs {e}⊆B:=
    (ordinaryResourceHubs_mono hsingInner).trans (ordinaryRootResources_hubs Inner B)
  have heterm:e∈ordinaryRootResources Wterm B:=
    ordinaryRootResources_contains {e} Wterm B hrow hhub (Finset.mem_singleton_self e)
  exact Finset.disjoint_left.mp havoid he heterm
end Oberwolfach
