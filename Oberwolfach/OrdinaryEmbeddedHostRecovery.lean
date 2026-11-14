module

public import Oberwolfach.OrdinaryGraphPairEmbeddings

@[expose] public section
/-! Recover supported graph pairs exactly from their restrictions to the
original rim and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]

theorem graph_comap_map_of_supported (φ:V↪W) (Q:SimpleGraph W)
    (hQ:∀v w,Q.Adj v w→v∈Set.range φ ∧ w∈Set.range φ):
    (Q.comap φ).map φ=Q:=by
  ext v w
  constructor
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj φ _ _ _).mp h
    exact hab
  · intro h
    obtain ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩:=hQ v w h
    exact SimpleGraph.map_adj_apply.mpr h

theorem ordinary_mapped_spokes_of_supported (φ:V↪W) (ψ:U↪Z) (H:W→Z→Prop)
    (hH:∀v u,H v u→v∈Set.range φ ∧ u∈Set.range ψ):
    ordinaryMappedSpokes (fun v u=>H (φ v) (ψ u)) φ ψ=H:=by
  funext v u
  apply propext
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩;exact hab
  · intro h
    obtain ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩:=hH v u h
    exact ⟨a,b,h,rfl,rfl⟩
end Oberwolfach
