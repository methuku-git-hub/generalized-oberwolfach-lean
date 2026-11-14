module

public import Oberwolfach.MarkedSpokeLoadGrouping
public import Oberwolfach.MarkedActualWheelPacking

@[expose] public section

/-! Determine which old hub can occur at a label on a prescribed spoke
path. Other paths have disjoint labels, and the rim/vertex wheels use fresh
hubs; no injectivity of the map on old hubs is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 13000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K S:Type} [Fintype V] [Fintype S] [DecidableEq V] [DecidableEq U] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_spoke_path_family_old_hub (m:ℕ)
    (p:S→(Fin m↪V)) (row:S→V) (hub:S→U) (ψ:U→U) (j:S→Bool)
    (W:S→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hW:∀ s i,(W s).1.val i=rootedCycleOrder (markedRootOrder m (j s)) (row s) (p s) i)
    (hWu:∀ s,(W s).2.val=ψ (hub s))
    (hR:∀ s t k,p s k≠row t)
    (hdis:∀ s t,s≠t→Disjoint (Finset.univ.image (p s)) (Finset.univ.image (p t))):
    ∀ u v,v∈spokePathHubVertices m p hub u→∀ z,
      (Sum.inr (v,z):Finset V⊕(V×U))∈Finset.univ.biUnion (fun s=>markedWheelPhysicalResources (W s))→z=ψ u:=by
  intro u v hv z hz
  obtain ⟨s,_,hsv⟩:=Finset.mem_biUnion.mp hv
  obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hsv
  obtain ⟨t,_,ht⟩:=Finset.mem_biUnion.mp hz
  have ht':=(markedWheelPhysicalResources_spoke (W t) v z).mp ht
  have htval:v=row t∨v∈Finset.univ.image (p t):=by
    have hval:=ht'.2
    rw [funext (hW t),rootedCycleOrder_vertices] at hval
    exact Finset.mem_insert.mp hval
  have hst:s.val=t:=by
    rcases htval with hr|htval
    · exact False.elim (hR s.val t k (hk.trans hr))
    · by_contra hn
      exact Finset.disjoint_left.mp (hdis s.val t hn) hsv htval
  exact ht'.1.symm.trans ((hWu t).trans (congrArg ψ (hst ▸ s.property)))

 theorem marked_fresh_hub_family_avoids_spoke {m:ℕ} {J:Type} [Fintype J]
    (W:J→MarkedWheel tail head ktail khead m π b H₀ HK) (B:Finset U)
    (hW:∀ j,(W j).2.val∉B) (v:V) (u:U) (hu:u∈B):
    (Sum.inr (v,u):Finset V⊕(V×U))∉Finset.univ.biUnion (fun j=>markedWheelPhysicalResources (W j)):=by
  intro he
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp he
  have hh:=(markedWheelPhysicalResources_spoke (W j) v u).mp hj
  exact hW j (hh.1 ▸ hu)

end Oberwolfach
