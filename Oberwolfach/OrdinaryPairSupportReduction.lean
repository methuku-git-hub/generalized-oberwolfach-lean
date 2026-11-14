module

public import Oberwolfach.OrdinaryEmbeddedPairDegrees

@[expose] public section

/-! Remove isolated row and hub labels before the finite absorber
construction. The original physical graph pair is recovered exactly by
embedding the reduced pair back into its ambient vertex types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

abbrev OrdinaryActiveRow (G : SimpleGraph V) := {v : V // v∈G.support}
abbrev OrdinaryActiveHub (H : V → U → Prop) := {u : U // ∃ v,H v u}
def ordinaryActiveRowEmbedding (G : SimpleGraph V) : OrdinaryActiveRow G ↪ V := Function.Embedding.subtype _
def ordinaryActiveHubEmbedding (H : V → U → Prop) : OrdinaryActiveHub H ↪ U := Function.Embedding.subtype _
def ordinarySupportRim (G : SimpleGraph V) : SimpleGraph (OrdinaryActiveRow G) := G.induce G.support
def ordinarySupportSpokes (G : SimpleGraph V) (H : V → U → Prop)
    (v : OrdinaryActiveRow G) (u : OrdinaryActiveHub H) : Prop := H v.val u.val

theorem ordinarySupportRim_map (G : SimpleGraph V) :
    (ordinarySupportRim G).map (ordinaryActiveRowEmbedding G)=G := by
  apply SimpleGraph.ext
  funext v w
  apply propext
  constructor
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
    exact hab
  · intro h
    exact (SimpleGraph.map_adj _ _ _ _).mpr
      ⟨⟨v,h.mem_support_left⟩,⟨w,h.mem_support_right⟩,h,rfl,rfl⟩

theorem balanced_spoke_row_support (G : SimpleGraph V) (H : V → U → Prop)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (v : V) (u : U) (hvu : H v u) : v∈G.support := by
  have hh : 0<(Finset.univ.filter (H v)).card :=
    Finset.card_pos.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvu⟩⟩
  by_contra hv
  have hz := (G.degree_eq_zero_iff_notMem_support v).mpr hv
  have hb := hbal v
  omega

theorem ordinarySupportSpokes_map (G : SimpleGraph V) (H : V → U → Prop)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card) :
    ordinaryMappedSpokes (ordinarySupportSpokes G H) (ordinaryActiveRowEmbedding G)
      (ordinaryActiveHubEmbedding H)=H := by
  funext v u
  apply propext
  constructor
  · rintro ⟨a,b,h,rfl,rfl⟩;exact h
  · intro h
    exact ⟨⟨v,balanced_spoke_row_support G H hbal v u h⟩,⟨u,v,h⟩,h,rfl,rfl⟩

theorem ordinarySupport_balance_divisibility (G : SimpleGraph V) (H : V → U → Prop) (r : ℕ)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv : ∀ u,r∣(Finset.univ.filter (fun v=>H v u)).card) :
    (∀ v,(ordinarySupportRim G).degree v=2*(Finset.univ.filter (ordinarySupportSpokes G H v)).card) ∧
    (∀ u,r∣(Finset.univ.filter (fun v=>ordinarySupportSpokes G H v u)).card) := by
  have heH := ordinarySupportSpokes_map G H hbal
  constructor
  · intro v
    have hd := SimpleGraph.degree_map_apply (ordinarySupportRim G) (ordinaryActiveRowEmbedding G) v
    simp only [←SimpleGraph.ncard_neighborSet] at hd
    rw [ordinarySupportRim_map] at hd
    simp only [SimpleGraph.ncard_neighborSet] at hd
    have hh := congrArg Finset.card (ordinaryMappedSpokes_row (ordinarySupportSpokes G H)
      (ordinaryActiveRowEmbedding G) (ordinaryActiveHubEmbedding H) v)
    rw [heH,Finset.card_image_of_injective _ (ordinaryActiveHubEmbedding H).injective] at hh
    rw [←hd,←hh]
    exact hbal v.val
  · intro u
    have hh := congrArg Finset.card (ordinaryMappedSpokes_column (ordinarySupportSpokes G H)
      (ordinaryActiveRowEmbedding G) (ordinaryActiveHubEmbedding H) u)
    rw [heH,Finset.card_image_of_injective _ (ordinaryActiveRowEmbedding G).injective] at hh
    rw [←hh]
    exact hdiv u.val

end Oberwolfach
