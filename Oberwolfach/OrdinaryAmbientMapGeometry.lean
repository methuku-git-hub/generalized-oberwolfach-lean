module

public import Oberwolfach.OrdinaryAmbientResourceMaps

@[expose] public section

/-! Root locations, disjointness and four-vertex separation for the actual
ambient maps induced by finite source-to-target maps. The vertex maps may
identify source vertices; only the two embedded vertex ranges are disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C D V U : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinaryAmbientMap_support_location (G : SimpleGraph A) (i : A ↪ V) (j : B ↪ V)
    (f : A → B) (R : Finset V) (hi : ∀ a,i a∈R) (hj : ∀ b,j b∈R) :
    ∀ v∈(G.map i).support,v∈R ∧ ordinaryAmbientMap i j f v∈R := by
  intro v hv
  rw [SimpleGraph.support_map] at hv
  obtain ⟨a,ha,rfl⟩ := hv
  exact ⟨hi a,by rw [ordinaryAmbientMap_apply];exact hj (f a)⟩

theorem ordinaryAmbientMap_disjoint_support (G : SimpleGraph A) (i : A ↪ V) (j : B ↪ V)
    (f : A → B) (hd : ∀ a b,i a≠j b) :
    ∀ v∈(G.map i).support,∀ w∈(G.map i).support,ordinaryAmbientMap i j f v≠w := by
  intro v hv w hw
  rw [SimpleGraph.support_map] at hv hw
  obtain ⟨a,ha,rfl⟩:=hv
  obtain ⟨b,hb,rfl⟩:=hw
  rw [ordinaryAmbientMap_apply]
  exact (hd b (f a)).symm

theorem ordinaryAmbientMap_active_hub_ne (H : A → C → Prop)
    (i : A ↪ V) (s : C ↪ U) (t : D ↪ U) (g : C → D)
    (hd : ∀ c d,s c≠t d) :
    ∀ u,(∃ v,ordinaryMappedSpokes H i s v u)→u≠ordinaryAmbientMap s t g u := by
  rintro u ⟨v,a,c,h,hv,rfl⟩
  rw [ordinaryAmbientMap_apply]
  exact hd c (g c)

theorem ordinaryAmbientMap_edge_roots_separated (G : SimpleGraph A) (F : SimpleGraph V)
    (i : A ↪ V) (j : B ↪ V) (f : A → B)
    (h₀ : ∀ a b,G.Adj a b→¬F.Adj (i a) (i b))
    (h₁ : ∀ a b,G.Adj a b→¬F.Adj (j (f a)) (j (f b)))
    (hcross : ∀ a b,¬F.Adj (i a) (j b)) :
    ∀ v w,(G.map i).Adj v w→
      ∀ a∈({v,w,ordinaryAmbientMap i j f v,ordinaryAmbientMap i j f w}:Finset V),
      ∀ b∈({v,w,ordinaryAmbientMap i j f v,ordinaryAmbientMap i j f w}:Finset V),¬F.Adj a b := by
  intro v w hvw
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hvw
  rw [ordinaryAmbientMap_apply,ordinaryAmbientMap_apply]
  have hxx : ¬F.Adj (i x) (i x) := fun h=>h.ne rfl
  have hyy : ¬F.Adj (i y) (i y) := fun h=>h.ne rfl
  have hffx : ¬F.Adj (j (f x)) (j (f x)) := fun h=>h.ne rfl
  have hffy : ¬F.Adj (j (f y)) (j (f y)) := fun h=>h.ne rfl
  intro a ha b hb
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl
  all_goals first | assumption | exact h₀ x y hxy | exact h₀ y x hxy.symm |
    exact h₁ x y hxy | exact h₁ y x hxy.symm | exact hcross _ _ |
    exact fun h=>hcross _ _ h.symm

end Oberwolfach
