module

public import Oberwolfach.OrdinaryPreCoverPackingData

@[expose] public section
/-! Compact assumptions for the pre-cover to post-cover packing bridge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

structure OrdinaryPreCoverPackingInputs
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) where
  graph_sub:Q≤P\F
  fields:OrdinaryEditedParentFields r hr k α βparent b B h δ εparent P Q F H
  geometry:OrdinaryUnreservedNearGeometryData r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c
    (Q\C.comap Sum.inl) F (fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u)) X Z σ
  cover_degree:∀a,(C.degree a:ℝ)≤L
  scale_V:L+(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card V
  scale_U:L+(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card U

theorem ordinary_precover_packing_data_of_inputs
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (d:OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L
      P Q F H X Z C σ):
    let Q':=Q\C.comap Sum.inl;let H':=fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u);
    let R:=retainedGraph (ordinaryBoundaryGraph Q' H' X Z) σ;
    Nonempty (OrdinaryNearBalancePackingData r hr k α ω β b B (h-ξ-ζ) δ εstar η P
      (ordinaryUnreservedRim Q' X R) F (ordinaryUnreservedSpokes H' X Z R)):=by
  exact ordinary_precover_unreserved_packing_data r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L
    P Q F H X Z C σ d.graph_sub d.fields d.geometry d.cover_degree d.scale_V d.scale_U
end Oberwolfach
