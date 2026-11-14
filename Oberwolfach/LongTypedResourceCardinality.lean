module

public import Oberwolfach.MarkedRawSampledPhysicalEmbedding

@[expose] public section
/-! Polynomial bounds for the actual typed resource universe, independent of
which raw resources are active. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_typed_resource_card_le_cube (n:ℕ) (hn:4≤n) (U:Type) [Fintype U]
    (hu:Fintype.card U≤n):
    Fintype.card ((((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))≤n^3 := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  nlinarith

theorem long_active_typed_resource_card_le_cube (n:ℕ) (hn:4≤n) (U:Type) [Fintype U]
    (hu:Fintype.card U≤n) (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool):
    Fintype.card {z // z∈bernoulliVertexSet state}≤n^3 := by
  exact le_trans (Fintype.card_subtype_le _) (long_typed_resource_card_le_cube n hn U hu)
end Oberwolfach
