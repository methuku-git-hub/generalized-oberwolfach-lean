module

public import Oberwolfach.OrdinaryLocalCycles
public import Oberwolfach.FractionalRelabeling

@[expose] public section
/-! Map an actual local cycle through an injective vertex embedding while
preserving its support and conflict-freeness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {r:ℕ}

def ordinaryLocalCycleMap (e:V↪W) (Q F:SimpleGraph V) (T:Finset V)
    (C:LocalOrdinaryCycle Q F T r):
    LocalOrdinaryCycle (Q.map e) (F.map e) (T.image e) r:=by
  let G:=C.val.val.val
  have hcycle:IsEmbeddedCycle (G.map e) r:=C.val.val.property.map e
  have hhost:G.map e≤Q.map e:=SimpleGraph.map_monotone e C.val.property
  refine ⟨⟨⟨G.map e,hcycle⟩,hhost⟩,?_,?_⟩
  · intro z hz
    rw [SimpleGraph.support_map] at hz
    obtain ⟨v,hv,rfl⟩:=hz
    exact Finset.mem_image.mpr ⟨v,C.property.1 v hv,rfl⟩
  · intro z hz w hw hf
    rw [SimpleGraph.support_map] at hz hw
    obtain ⟨v,hv,rfl⟩:=hz
    obtain ⟨v',hv',rfl⟩:=hw
    exact C.property.2 v hv v' hv' (SimpleGraph.map_adj_apply.mp hf)

theorem ordinary_local_cycle_map_vertices (e:V↪W) (Q F:SimpleGraph V) (T:Finset V)
    (C:LocalOrdinaryCycle Q F T r):
    localOrdinaryVertices (ordinaryLocalCycleMap e Q F T C)=(localOrdinaryVertices C).image e:=by
  ext z
  simp only [localOrdinaryVertices,Set.mem_toFinset,ordinaryLocalCycleMap,SimpleGraph.support_map,
    Set.mem_image,Finset.mem_image]

theorem ordinary_local_cycle_map_injective (e:V↪W) (Q F:SimpleGraph V) (T:Finset V):
    Function.Injective (ordinaryLocalCycleMap (r:=r) e Q F T):=by
  intro C D h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply SimpleGraph.map_injective e
  exact congrArg (fun C=>C.val.val.val) h
end Oberwolfach
