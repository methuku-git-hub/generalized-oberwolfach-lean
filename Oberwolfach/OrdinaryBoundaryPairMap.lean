module

public import Oberwolfach.OrdinaryPhysicalPairMap
public import Oberwolfach.OrdinaryDeepBoundaryFourPieces

@[expose] public section
/-! Inner-pair and boundary restrictions commute with injective physical maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_inner_vertices_image (T:Finset V) (W:Finset U) (φ:V↪V') (ψ:U↪U'):
    (ordinaryInnerVertices T W).image (φ.sumMap ψ)=ordinaryInnerVertices (T.image φ) (W.image ψ):=by
  ext a
  cases a <;> simp [ordinaryInnerVertices,Finset.mem_image] <;> aesop

theorem ordinary_boundary_pair_map (Q:SimpleGraph V) (H:V→U→Prop)
    (T:Finset V) (W:Finset U) (φ:V↪V') (ψ:U↪U'):
    ordinaryBoundaryGraph (Q.map φ) (ordinaryMappedSpokes H φ ψ) (T.image φ) (W.image ψ)=
      (ordinaryBoundaryGraph Q H T W).map (φ.sumMap ψ):=by
  let e:=φ.sumMap ψ
  have hm (a:V⊕U):e a∈ordinaryInnerVertices (T.image φ) (W.image ψ) ↔ a∈ordinaryInnerVertices T W:=by
    rw [←ordinary_inner_vertices_image T W φ ψ]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨b,hb,h⟩
      exact e.injective h ▸ hb
    · intro h
      exact ⟨a,h,rfl⟩
  ext x y
  constructor
  · intro hxy
    have hh:=(ordinaryBoundaryGraph_adj _ _ _ _ x y).mp hxy
    rw [ordinary_physical_pair_map] at hh
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj e (ordinaryPhysicalGraph Q H) x y).mp hh.1
    have hc:=hh.2
    rw [hm a,hm b] at hc
    exact SimpleGraph.map_adj_apply.mpr ((ordinaryBoundaryGraph_adj Q H T W a b).mpr ⟨hab,hc⟩)
  · intro hxy
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj e (ordinaryBoundaryGraph Q H T W) x y).mp hxy
    have hh:=(ordinaryBoundaryGraph_adj Q H T W a b).mp hab
    apply (ordinaryBoundaryGraph_adj _ _ _ _ (e a) (e b)).mpr
    constructor
    · rw [ordinary_physical_pair_map]
      exact SimpleGraph.map_adj_apply.mpr hh.1
    · rw [hm a,hm b]
      exact hh.2
end Oberwolfach
