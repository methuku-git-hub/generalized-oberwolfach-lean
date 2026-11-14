module

public import Oberwolfach.OrdinaryEmbeddedPairDegrees

@[expose] public section

/-! The transformer root-degree and active-hub bounds are measured on
the finite source pair, even though its embedding has ambient vertex types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' : Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_embedded_spoke_column_bound (H : V → U → Prop) (i : V ↪ V') (j : U ↪ U') :
    ∀ u,(Finset.univ.filter (fun v=>ordinaryMappedSpokes H i j v u)).card≤Fintype.card V := by
  intro u
  by_cases hu : u∈Set.range j
  · obtain ⟨a,rfl⟩:=hu
    rw [ordinaryMappedSpokes_column,Finset.card_image_of_injective _ i.injective]
    exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  · rw [ordinaryMappedSpokes_column_outside H i j u hu]
    exact Nat.zero_le _

theorem ordinary_embedded_active_hub_bound (H : V → U → Prop) (i : V ↪ V') (j : U ↪ U') :
    Fintype.card {u:U' // ∃ v,ordinaryMappedSpokes H i j v u}≤Fintype.card U := by
  rw [Fintype.card_subtype]
  have hs : (Finset.univ.filter (fun u:U'=>∃ v,ordinaryMappedSpokes H i j v u))⊆Finset.univ.image j := by
    intro u hu
    obtain ⟨v,a,b,h,hv,hu⟩ := (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hu⟩
  exact (Finset.card_le_card hs).trans_eq (by rw [Finset.card_image_of_injective _ j.injective,Finset.card_univ])

end Oberwolfach
