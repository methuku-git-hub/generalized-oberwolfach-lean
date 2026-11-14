module

public import Oberwolfach.OrdinaryRawPairStateEquality

@[expose] public section
/-! Induced target-neighbour counts equal the corresponding ambient counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem ordinary_comap_target_neighbour_image (P:SimpleGraph V) (f:W↪V) (D:Finset W) (x:W):
    (D∩(P.comap f).neighborFinset x).image f=(D.image f)∩P.neighborFinset (f x):=by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
    have hw':=Finset.mem_inter.mp hw
    have hn:f w∈P.neighborFinset (f x):=by
      simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj] using hw'.2
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨w,hw'.1,rfl⟩,hn⟩
  · intro hv
    obtain ⟨hv,hneigh⟩:=Finset.mem_inter.mp hv
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
    have hn:w∈(P.comap f).neighborFinset x:=by
      simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj] using hneigh
    exact Finset.mem_image.mpr ⟨w,Finset.mem_inter.mpr ⟨hw,hn⟩,rfl⟩

theorem ordinary_comap_target_neighbour_card (P:SimpleGraph V) (f:W↪V) (D:Finset W) (x:W):
    (D∩(P.comap f).neighborFinset x).card=((D.image f)∩P.neighborFinset (f x)).card:=by
  have hh:=congrArg Finset.card (ordinary_comap_target_neighbour_image P f D x)
  simpa only [Finset.card_image_of_injective _ f.injective] using hh
end Oberwolfach
