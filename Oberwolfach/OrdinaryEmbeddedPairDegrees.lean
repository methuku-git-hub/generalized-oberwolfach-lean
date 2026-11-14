module

public import Oberwolfach.OrdinaryGraphPairEmbeddings

@[expose] public section

/-! Exact row and hub degrees after embedding a finite graph pair into
an ambient host. Vertices outside the image are isolated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' : Type*} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinaryMappedSpokes_row (H : V → U → Prop) (φ : V ↪ V') (ψ : U ↪ U') (v : V) :
    (Finset.univ.filter (ordinaryMappedSpokes H φ ψ (φ v)))=(Finset.univ.filter (H v)).image ψ := by
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨v',u,h,he,hu⟩
    rw [φ.injective he] at h
    exact ⟨u,h,hu⟩
  · rintro ⟨u,h,hu⟩
    exact ⟨v,u,h,rfl,hu⟩

theorem ordinaryMappedSpokes_column (H : V → U → Prop) (φ : V ↪ V') (ψ : U ↪ U') (u : U) :
    (Finset.univ.filter (fun a => ordinaryMappedSpokes H φ ψ a (ψ u)))=
      (Finset.univ.filter (fun v => H v u)).image φ := by
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨v,u',h,hv,he⟩
    rw [ψ.injective he] at h
    exact ⟨v,h,hv⟩
  · rintro ⟨v,h,hv⟩
    exact ⟨v,u,h,hv,rfl⟩

theorem ordinaryMappedSpokes_row_outside (H : V → U → Prop) (φ : V ↪ V') (ψ : U ↪ U')
    (a : V') (ha : a∉Set.range φ) : Finset.univ.filter (ordinaryMappedSpokes H φ ψ a)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨v,u,h,hv,hu⟩ := (Finset.mem_filter.mp hb).2
  exact ha ⟨v,hv⟩

theorem ordinaryMappedSpokes_column_outside (H : V → U → Prop) (φ : V ↪ V') (ψ : U ↪ U')
    (b : U') (hb : b∉Set.range ψ) : Finset.univ.filter (fun a => ordinaryMappedSpokes H φ ψ a b)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨v,u,h,hv,hu⟩ := (Finset.mem_filter.mp ha).2
  exact hb ⟨u,hu⟩

theorem simpleGraph_map_degree_outside (G : SimpleGraph V) (φ : V ↪ V') (a : V')
    (ha : a∉Set.range φ) : (G.map φ).degree a=0 := by
  apply ((G.map φ).degree_eq_zero_iff_notMem_support a).mpr
  rw [SimpleGraph.support_map]
  rintro ⟨v,hv,hva⟩
  exact ha ⟨v,hva⟩

theorem ordinary_pair_embedding_balance (G : SimpleGraph V) (H : V → U → Prop)
    (φ : V ↪ V') (ψ : U ↪ U')
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card) :
    ∀ a,(G.map φ).degree a=2*(Finset.univ.filter (ordinaryMappedSpokes H φ ψ a)).card := by
  intro a
  by_cases ha : a∈Set.range φ
  · obtain ⟨v,rfl⟩ := ha
    rw [SimpleGraph.degree_map_apply,ordinaryMappedSpokes_row,Finset.card_image_of_injective _ ψ.injective]
    exact hbal v
  · rw [simpleGraph_map_degree_outside G φ a ha,ordinaryMappedSpokes_row_outside H φ ψ a ha]
    simp

theorem ordinary_pair_embedding_divisibility (H : V → U → Prop) (φ : V ↪ V') (ψ : U ↪ U')
    (r : ℕ) (hdiv : ∀ u,r∣(Finset.univ.filter (fun v => H v u)).card) :
    ∀ b,r∣(Finset.univ.filter (fun a => ordinaryMappedSpokes H φ ψ a b)).card := by
  intro b
  by_cases hb : b∈Set.range ψ
  · obtain ⟨u,rfl⟩ := hb
    rw [ordinaryMappedSpokes_column,Finset.card_image_of_injective _ φ.injective]
    exact hdiv u
  · rw [ordinaryMappedSpokes_column_outside H φ ψ b hb]
    simp

end Oberwolfach
