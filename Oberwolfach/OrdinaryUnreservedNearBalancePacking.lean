module

public import Oberwolfach.OrdinaryNearBalancePackingData
public import Oberwolfach.OrdinaryPackingCleanupData

@[expose] public section
/-! Apply the near-balance packing theorem to the actual host outside the
inner pair and fresh reserve, retaining its original structural hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_near_balance_packing (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bminus bplus h δ:ℝ,
      0<ω→0<β→0<bminus→0<bplus→0<h→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀γ:ℝ,0<γ→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],n₀≤Fintype.card V→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)),
    OrdinaryNearBalancePackingData r hr k α ω β bminus bplus h δ εstar η P
      (ordinaryUnreservedRim Q X R) F (ordinaryUnreservedSpokes H X Z R)→
    Nonempty (OrdinaryUnreservedPackingData Q F H X Z R r (γ*Fintype.card (V⊕U))):=by
  obtain ⟨N,hN⟩:=ordinary_near_balance_wheel_packing r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β bminus bplus h δ hω hβ hbm hbp hh hδ hδ1
  obtain ⟨εstar,hεstar,hpack⟩:=hN k hk ω β bminus bplus h δ hω hβ hbm hbp hh hδ hδ1
  refine ⟨εstar,hεstar,?_⟩
  intro γ hγ
  obtain ⟨η,hη,n₀,hηpack⟩:=hpack γ hγ
  refine ⟨η,hη,n₀,?_⟩
  intro V U _ _ _ _ hn P Q F H X Z R data
  obtain ⟨M,hM,hleft⟩:=hηpack V U hn data.hub_lower data.hub_upper P (ordinaryUnreservedRim Q X R) F
    (ordinaryUnreservedSpokes H X Z R) data.orientation data.graph_sub data.orientation_graph data.rim_cuts
    data.spoke_cuts data.spoke_degree data.balance data.isolators data.transfers data.weight data.weight_bounds
    data.rim_load data.spoke_load
  refine ⟨⟨M,hM,?_⟩⟩
  intro w
  have hnVW:(Fintype.card V:ℝ)≤Fintype.card (V⊕U):=Nat.cast_le.mpr
    (Fintype.card_le_of_injective Sum.inl Sum.inl_injective)
  exact (hleft w).trans (mul_le_mul_of_nonneg_left hnVW hγ.le)
end Oberwolfach
