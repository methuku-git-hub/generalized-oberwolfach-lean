module

public import Oberwolfach.OrdinaryTwoDomainChangeGeometry

@[expose] public section
/-! Transfer the exact restricted row and column edit budgets to the
one-type auxiliary graph used by the triangle sampling event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_two_domain_restricted_change_bounds
    (R Q:SimpleGraph V) (H J:V→U→Prop) (A:Finset V) (B:Finset U) (L:ℝ) (hL:0≤L)
    (hR:∀v,((changed (A∩R.neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L)
    (hrow:∀v,((changed (B.filter (H v)) (B.filter (J v))).card:ℝ)≤L)
    (hcol:∀u∈B,((changed (A.filter (fun v=>H v u)) (A.filter (fun v=>J v u))).card:ℝ)≤L):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let A':=A.image (Sum.inl:V→V⊕U)
    let B':=B.image (Sum.inr:U→V⊕U);
    (∀z,((changed (A'∩(R.map e).neighborFinset z) (A'∩(Q.map e).neighborFinset z)).card:ℝ)≤L) ∧
    (∀z,((changed (B'∩(ordinaryPhysicalSpokeGraph H).neighborFinset z)
      (B'∩(ordinaryPhysicalSpokeGraph J).neighborFinset z)).card:ℝ)≤L) ∧
    (∀z∈B',((changed (A'∩(ordinaryPhysicalSpokeGraph H).neighborFinset z)
      (A'∩(ordinaryPhysicalSpokeGraph J).neighborFinset z)).card:ℝ)≤L):=by
  intro e A' B'
  constructor
  · intro z
    cases z with
    | inl v=>
      rw [ordinary_sum_rim_neighbours,ordinary_sum_rim_neighbours,changed_image_card _ Sum.inl_injective]
      exact hR v
    | inr u=>
      rw [ordinary_sum_rim_neighbours_hub,ordinary_sum_rim_neighbours_hub]
      simpa [changed] using hL
  constructor
  · intro z
    cases z with
    | inl v=>
      rw [ordinary_sum_spoke_row_neighbours,ordinary_sum_spoke_row_neighbours,changed_image_card _ Sum.inr_injective]
      exact hrow v
    | inr u=>
      rw [ordinary_sum_spoke_row_neighbours_hub,ordinary_sum_spoke_row_neighbours_hub]
      simpa [changed] using hL
  · intro z hz
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
    rw [ordinary_sum_spoke_column_neighbours,ordinary_sum_spoke_column_neighbours,changed_image_card _ Sum.inl_injective]
    exact hcol u hu
end Oberwolfach
