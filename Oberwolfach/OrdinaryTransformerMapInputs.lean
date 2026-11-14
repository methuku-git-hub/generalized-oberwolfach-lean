module

public import Oberwolfach.OrdinaryAmbientResourceMaps

@[expose] public section

/-! Extract the actual edge-injectivity and adjacency premises of the
ordinary transformer from a physical resource bijection. Vertex maps
may identify different old vertices, as the expansion collapses do. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_resource_map_rim_injective (G : SimpleGraph V) [DecidableRel G.Adj] (H : V → U → Prop) (f : V → V) (g : U → U)
    (h : Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources G H)) :
    Function.Injective (fun i:G.edgeFinset => s(f i.val.out.1,f i.val.out.2)) := by
  intro i j he
  have hmap (a : Sym2 V) : Sym2.map f a=s(f a.out.1,f a.out.2) := by
    calc
      _ = Sym2.map f s(a.out.1,a.out.2) := congrArg (Sym2.map f) a.out_eq.symm
      _ = _ := rfl
  have hi : Sum.inl i.val∈ordinaryHostResources G H := (ordinaryHostResources_rim _ _ _).mpr
    (by simpa only [SimpleGraph.mem_edgeFinset] using i.property)
  have hj : Sum.inl j.val∈ordinaryHostResources G H := (ordinaryHostResources_rim _ _ _).mpr
    (by simpa only [SimpleGraph.mem_edgeFinset] using j.property)
  have he' : ordinaryPairResourceMap f g (.inl i.val)=ordinaryPairResourceMap f g (.inl j.val) := by
    change Sum.inl (Sym2.map f i.val)=Sum.inl (Sym2.map f j.val)
    rw [hmap,hmap]
    exact congrArg Sum.inl he
  exact Subtype.ext (Sum.inl.inj (h hi hj he'))

theorem ordinary_resource_map_spoke_injective (G : SimpleGraph V) (H : V → U → Prop) (f : V → V) (g : U → U)
    (h : Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources G H)) :
    Function.Injective (fun i:{e:V×U // H e.1 e.2} => (f i.val.1,g i.val.2)) := by
  intro i j he
  have hi := (ordinaryHostResources_spoke G H i.val.1 i.val.2).mpr i.property
  have hj := (ordinaryHostResources_spoke G H j.val.1 j.val.2).mpr j.property
  exact Subtype.ext (Sum.inr.inj (h hi hj (congrArg Sum.inr he)))

theorem ordinary_resource_image_rim_hom (G P : SimpleGraph V) (H K : V → U → Prop) (f : V → V) (g : U → U)
    (himage : transformerImageResources G H f g=ordinaryHostResources P K) :
    ∀ v w,G.Adj v w → P.Adj (f v) (f w) := by
  intro v w hvw
  have hh : ordinaryPairResourceMap f g (.inl s(v,w))∈transformerImageResources G H f g := by
    rw [transformerImageResources_eq_image]
    exact Finset.mem_image.mpr ⟨.inl s(v,w),(ordinaryHostResources_rim _ _ _).mpr hvw,rfl⟩
  rw [himage] at hh
  exact (ordinaryHostResources_rim _ _ _).mp hh

theorem ordinary_resource_image_spoke_hom (G P : SimpleGraph V) (H K : V → U → Prop) (f : V → V) (g : U → U)
    (himage : transformerImageResources G H f g=ordinaryHostResources P K) :
    ∀ v u,H v u → K (f v) (g u) := by
  intro v u hvu
  have hh : ordinaryPairResourceMap f g (.inr (v,u))∈transformerImageResources G H f g := by
    rw [transformerImageResources_eq_image]
    exact Finset.mem_image.mpr ⟨.inr (v,u),(ordinaryHostResources_spoke _ _ _ _).mpr hvu,rfl⟩
  rw [himage] at hh
  exact (ordinaryHostResources_spoke _ _ _ _).mp hh

end Oberwolfach
