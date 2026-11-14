module

public import Oberwolfach.OrdinaryLocalCycleEmbedding
public import Oberwolfach.OrdinaryCycleInEmbeddedDomain

@[expose] public section
/-! Every local cycle in an embedded host comes uniquely from the original
domain, preserving its graph and vertex support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {r:ℕ}

theorem ordinary_local_cycle_map_surjective (e:V↪W) (Q F:SimpleGraph V) (T:Finset V):
    Function.Surjective (ordinaryLocalCycleMap (r:=r) e Q F T):=by
  intro C
  obtain ⟨G,hG,hGQ,hmap⟩:=ordinary_cycle_in_embedded_domain e Q C.val.val.val r C.val.val.property C.val.property
  have hmem (v:V) (hv:v∈G.support):e v∈C.val.val.val.support:=by
    rw [←hmap,SimpleGraph.support_map]
    exact ⟨v,hv,rfl⟩
  have hT:∀v∈G.support,v∈T:=by
    intro v hv
    have hh:=C.property.1 (e v) (hmem v hv)
    obtain ⟨v',hv',he⟩:=Finset.mem_image.mp hh
    have hvv:v'=v:=e.injective he
    simpa [hvv] using hv'
  have hF:∀v∈G.support,∀w∈G.support,¬F.Adj v w:=by
    intro v hv w hw hf
    exact C.property.2 (e v) (hmem v hv) (e w) (hmem w hw) (SimpleGraph.map_adj_apply.mpr hf)
  let D:LocalOrdinaryCycle Q F T r:=⟨⟨⟨G,hG⟩,hGQ⟩,hT,hF⟩
  refine ⟨D,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hmap

def ordinaryLocalCycleEmbeddingEquiv (e:V↪W) (Q F:SimpleGraph V) (T:Finset V):
    LocalOrdinaryCycle Q F T r ≃ LocalOrdinaryCycle (Q.map e) (F.map e) (T.image e) r:=
  Equiv.ofBijective (ordinaryLocalCycleMap e Q F T)
    ⟨ordinary_local_cycle_map_injective e Q F T,ordinary_local_cycle_map_surjective e Q F T⟩
end Oberwolfach
