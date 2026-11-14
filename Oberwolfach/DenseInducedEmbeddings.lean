module

public import Oberwolfach.FixedPathCycles
public import Oberwolfach.InducedFractionalCycles
public import Oberwolfach.OrdinaryWheelResources

@[expose] public section

/-! Fixed-size embeddings inside a large prescribed vertex set. The
ambient order is retained in the minimum-degree hypothesis, and all
losses are charged to the actual omitted vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem induced_degree_delete_bound (G : SimpleGraph V) (A : Finset V) (v : (A:Set V)) :
    G.degree v.val ≤ (G.induce (A:Set V)).degree v+(Finset.univ\A).card := by
  rw [induced_degree_intersection]
  have he := Finset.card_inter_add_card_sdiff (G.neighborFinset v.val) A
  have hsub : G.neighborFinset v.val\A ⊆ Finset.univ\A := Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl
  have hh := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at he
  omega

theorem induced_dense_degree (G : SimpleGraph V) (A : Finset V) (n : ℕ) (β : ℝ)
    (hdeg : ∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v)
    (hA : ((Finset.univ\A).card:ℝ) ≤ (β/2)*n) (v : (A:Set V)) :
    (1/2+β/2)*(n:ℝ) ≤ (G.induce (A:Set V)).degree v := by
  have hh : (G.degree v.val:ℝ) ≤ (G.induce (A:Set V)).degree v+((Finset.univ\A).card:ℝ) := by
    exact_mod_cast induced_degree_delete_bound G A v
  linarith [hdeg v.val]

theorem fixed_cycle_inside_large_subset (β : ℝ) (hβ : 0 < β) (r b : ℕ) (hr : 3 ≤ r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (V : Type*) [Fintype V] [DecidableEq V],Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V),(∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) →
    ∀ (A S : Finset V),((Finset.univ\A).card:ℝ) ≤ (β/2)*n → S.card ≤ b →
    ∀ x : V,x∈A → x∉S →
    ∃ C : SimpleGraph V,IsEmbeddedCycle C r ∧ C ≤ G ∧ x∈C.support ∧
      C.support ⊆ (A:Set V) ∧ ∀ v∈C.support,v∉S := by
  obtain ⟨n₀,hembed⟩ := fixed_cycle_through_vertex (β/2) (by positivity) r b hr
  refine ⟨n₀,?_⟩
  intro n hn V _ _ hV G hdeg A S hA hS x hxA hxS
  let S' : Finset (A:Set V) := Finset.univ.filter (fun v => v.val∈S)
  have hS' : S'.card ≤ b := by
    let f : S' → S := fun v => ⟨v.val.val,(Finset.mem_filter.mp v.property).2⟩
    have hf : Function.Injective f := by
      intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : S => z.val) he
    have hh := Fintype.card_le_of_injective f hf
    have hh' : S'.card ≤ S.card := by simpa only [Fintype.card_coe] using hh
    exact hh'.trans hS
  have hAcard : Fintype.card (A:Set V) ≤ n := by
    simpa using (Finset.card_le_univ A).trans hV
  obtain ⟨C,hC,hCG,hxC,havoid⟩ := hembed n hn (A:Set V) hAcard (G.induce (A:Set V))
    (induced_dense_degree G A n β hdeg hA) ⟨x,hxA⟩ S' hS' (by simpa [S'] using hxS)
  let f : (A:Set V) ↪ V := Function.Embedding.subtype _
  let D := C.map f
  have hDG : D ≤ G := by
    have hh := SimpleGraph.map_monotone f hCG
    exact hh.trans (spanningRestriction_le G A)
  refine ⟨D,hC.map f,hDG,?_,?_,?_⟩
  · rw [show D=C.map f from rfl,C.support_map]
    exact ⟨⟨x,hxA⟩,hxC,rfl⟩
  · intro v hv
    rw [show D=C.map f from rfl,C.support_map] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact w.property
  · intro v hv
    rw [show D=C.map f from rfl,C.support_map] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    have hh := havoid w hw
    change w.val ∉ S
    simpa [S'] using hh

theorem fixed_hub_wheel_embedding (β : ℝ) (hβ : 0 < β) (r b : ℕ) (hr : 3 ≤ r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (V U : Type*) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) →
    ∀ (u : U),((Finset.univ.filter (fun v => ¬H v u)).card:ℝ) ≤ (β/2)*n →
    ∀ (x : V) (S : Finset V),H x u → S.card ≤ b → x∉S →
    ∃ W : OrdinaryWheel G ⊥ H r,ordinaryWheelHub W=u ∧ x∈(ordinaryWheelRim W).support ∧
      ∀ v∈(ordinaryWheelRim W).support,v∉S := by
  obtain ⟨n₀,hn₀⟩ := fixed_cycle_inside_large_subset β hβ r b hr
  refine ⟨n₀,?_⟩
  intro n hn V U _ _ _ _ hV G H hdeg u hu x S hxu hS hx
  let A := Finset.univ.filter (fun v => H v u)
  have hAc : ((Finset.univ\A).card:ℝ) ≤ (β/2)*n := by
    have he : Finset.univ\A=Finset.univ.filter (fun v => ¬H v u) := by ext v;simp [A]
    rwa [he]
  obtain ⟨C,hC,hCG,hxC,hCA,havoid⟩ := hn₀ n hn V hV G hdeg A S hAc hS x (by simp [A,hxu]) hx
  let W : OrdinaryWheel G ⊥ H r := ⟨(⟨⟨C,hC⟩,hCG⟩,u),
    (fun v hv => (Finset.mem_filter.mp (hCA hv)).2),fun _ _ _ _ => not_false⟩
  exact ⟨W,rfl,hxC,havoid⟩

end Oberwolfach
