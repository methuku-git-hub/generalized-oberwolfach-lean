module

public import Oberwolfach.PhysicalEdgeGraph
public import Oberwolfach.MappedFactorGraph

@[expose] public section

/-! The physical graph commutes with an injective vertex map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physicalEdgeGraph_image_map {W V:Type} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    (f:W↪V) (S:Finset (Finset W)):
    physicalEdgeGraph (S.image (fun e=>e.image f))=(physicalEdgeGraph S).map f:=by
  ext v z
  change (v≠z∧{v,z}∈S.image (fun e=>e.image f))↔_
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨hvz,he⟩
    obtain ⟨e,he,hpair⟩:=Finset.mem_image.mp he
    have hv:v∈e.image f:=by rw [hpair];exact Finset.mem_insert_self _ _
    have hz:z∈e.image f:=by rw [hpair];exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨x,hx,hfx⟩:=Finset.mem_image.mp hv
    obtain ⟨y,hy,hfy⟩:=Finset.mem_image.mp hz
    have hxy:x≠y:=by intro h;apply hvz;exact hfx.symm.trans ((congrArg f h).trans hfy)
    have heq:e={x,y}:=by
      apply Finset.image_injective f.injective
      simpa only [Finset.image_insert,Finset.image_singleton,hfx,hfy] using hpair
    exact ⟨x,y,⟨hxy,heq ▸ he⟩,hfx,hfy⟩
  · rintro ⟨x,y,hxy,rfl,rfl⟩
    refine ⟨fun he=>hxy.1 (f.injective he),Finset.mem_image.mpr ⟨{x,y},hxy.2,?_⟩⟩
    simp only [Finset.image_insert,Finset.image_singleton]

end Oberwolfach
