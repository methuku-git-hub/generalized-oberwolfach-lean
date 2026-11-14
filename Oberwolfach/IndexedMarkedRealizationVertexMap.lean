module

public import Oberwolfach.IndexedMarkedRealizationResources
public import Oberwolfach.IndexedMarkedRealizationGeometry

@[expose] public section

/-! Pull an actual realisation back along a displayed vertex map. The
edge indices are retained, so the physical resource set is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
variable {V₀ U₀ V₁ U₁ V U E K A S:Type}
    [Fintype V₀] [Fintype U₀] [Fintype V₁] [Fintype U₁] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}

def IndexedMarkedHostRealization.ofVertexMap
    (G:IndexedMarkedGraph V₀ U₀ A S) {G':IndexedMarkedGraph V₁ U₁ A S}
    (R:IndexedMarkedHostRealization G' tail head ktail khead H₀ HK π b)
    (f:V₀→V₁) (g:U₀→U₁) (he:G.map f g=G'):
    IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b:=
  .ofMapEq G R (R.rows∘f) (R.hubs∘g) (by rw [←IndexedMarkedGraph.map_map,he])

theorem IndexedMarkedHostRealization.resources_ofVertexMap
    (G:IndexedMarkedGraph V₀ U₀ A S) {G':IndexedMarkedGraph V₁ U₁ A S}
    (R:IndexedMarkedHostRealization G' tail head ktail khead H₀ HK π b)
    (f:V₀→V₁) (g:U₀→U₁) (he:G.map f g=G'):
    (IndexedMarkedHostRealization.ofVertexMap G R f g he).resources=R.resources:=
  IndexedMarkedHostRealization.resources_ofMapEq _ _ _ _ _

theorem IndexedMarkedHostRealization.sets_ofVertexMap
    (G:IndexedMarkedGraph V₀ U₀ A S) {G':IndexedMarkedGraph V₁ U₁ A S}
    (R:IndexedMarkedHostRealization G' tail head ktail khead H₀ HK π b)
    (f:V₀→V₁) (g:U₀→U₁) (he:G.map f g=G'):
    (IndexedMarkedHostRealization.ofVertexMap G R f g he).rowSet⊆R.rowSet∧
    (IndexedMarkedHostRealization.ofVertexMap G R f g he).hubSet⊆R.hubSet:=by
  constructor
  · intro v hv
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
    exact R.row_mem (f x)
  · intro v hv
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
    exact R.hub_mem (g x)

end Oberwolfach
