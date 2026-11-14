module

public import Oberwolfach.HypergraphRootColorSampling
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-! Padding each edge to a fixed rank with private vertices. Original
resources and parallel edge indices are retained without identification. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev UniformPaddingVertex {V E : Type*} (R : E → Finset V) (k : ℕ) :=
  V ⊕ (Σ e : E,Fin (k-(R e).card))

def uniformPaddingIncidence {V E : Type*} (R : E → Finset V) (k : ℕ) (e : E) :
    Finset (UniformPaddingVertex R k) := by
  classical
  exact (R e).map Function.Embedding.inl ∪ Finset.univ.map
    ⟨fun j : Fin (k-(R e).card)=>Sum.inr ⟨e,j⟩,fun _ _ h=>by simpa using Sum.inr.inj h⟩

theorem uniformPadding_original_mem {V E : Type*} (R : E → Finset V) (k : ℕ) (e : E) (v : V) :
    Sum.inl v∈uniformPaddingIncidence R k e ↔ v∈R e := by
  classical
  simp [uniformPaddingIncidence]

theorem uniformPadding_private_mem {V E : Type*} (R : E → Finset V) (k : ℕ)
    (e f : E) (j : Fin (k-(R f).card)) :
    Sum.inr ⟨f,j⟩∈uniformPaddingIncidence R k e ↔ e=f := by
  classical
  constructor
  · intro h
    simp only [uniformPaddingIncidence,Finset.mem_union,Finset.mem_map,Finset.mem_univ,true_and,
      Function.Embedding.inl_apply] at h
    rcases h with ⟨_,_,h⟩|⟨i,hi⟩
    · cases h
    · exact congrArg Sigma.fst (Sum.inr.inj hi)
  · intro h
    subst f
    apply Finset.mem_union_right
    exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem uniformPadding_card {V E : Type*} (R : E → Finset V) (k : ℕ)
    (hsize : ∀ e,(R e).card≤k) (e : E) : (uniformPaddingIncidence R k e).card=k := by
  classical
  have hd : Disjoint ((R e).map Function.Embedding.inl)
      (Finset.univ.map ⟨fun j : Fin (k-(R e).card)=>Sum.inr ⟨e,j⟩,
        fun _ _ h=>by simpa using Sum.inr.inj h⟩ : Finset (UniformPaddingVertex R k)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hy
    cases hji
  rw [uniformPaddingIncidence,Finset.card_union_of_disjoint hd]
  simp only [Finset.card_map,Finset.card_univ,Fintype.card_fin]
  have he := hsize e
  omega

theorem uniformPadding_degree_original {V E : Type*} [Fintype E]
    [DecidableEq V] (R : E → Finset V) (k : ℕ) (v : V) :
    Fintype.card (HypergraphEdgesAt (uniformPaddingIncidence R k) (Sum.inl v))=
      Fintype.card (HypergraphEdgesAt R v) := by
  classical
  simp only [HypergraphEdgesAt,Fintype.card_subtype,uniformPadding_original_mem]

theorem uniformPadding_degree_private {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (k : ℕ) (e : E) (j : Fin (k-(R e).card)) :
    Fintype.card (HypergraphEdgesAt (uniformPaddingIncidence R k) (Sum.inr ⟨e,j⟩))=1 := by
  classical
  simp only [HypergraphEdgesAt,Fintype.card_subtype,uniformPadding_private_mem]
  apply Finset.card_eq_one.mpr
  refine ⟨e,?_⟩
  ext f
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]

theorem uniformPadding_codegree_original {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (k : ℕ) (u v : V) :
    (Finset.univ.filter (fun e=>Sum.inl u∈uniformPaddingIncidence R k e ∧
      Sum.inl v∈uniformPaddingIncidence R k e)).card=
      (Finset.univ.filter (fun e=>u∈R e ∧ v∈R e)).card := by
  classical
  simp only [uniformPadding_original_mem]

theorem uniformPadding_codegree_private {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (k : ℕ) (v : UniformPaddingVertex R k)
    (e : E) (j : Fin (k-(R e).card)) :
    (Finset.univ.filter (fun f=>v∈uniformPaddingIncidence R k f ∧
      Sum.inr ⟨e,j⟩∈uniformPaddingIncidence R k f)).card≤1 := by
  classical
  calc
    _ ≤ ({e} : Finset E).card := Finset.card_le_card (by
      intro f hf
      exact Finset.mem_singleton.mpr ((uniformPadding_private_mem R k f e j).mp (Finset.mem_filter.mp hf).2.2))
    _ = 1 := Finset.card_singleton _

theorem uniformPadding_vertex_card {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (k : ℕ) :
    Fintype.card (UniformPaddingVertex R k)≤Fintype.card V+k*Fintype.card E := by
  classical
  simp only [UniformPaddingVertex,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]
  have hs := Finset.sum_le_sum (fun e (_ : e∈Finset.univ)=>Nat.sub_le k (R e).card)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using Nat.add_le_add_left hs (Fintype.card V)

theorem uniformPadding_matching_projection {V E : Type*} (R : E → Finset V) (k : ℕ) (M : Finset E)
    (hM : ∀ e∈M,∀ f∈M,e≠f → Disjoint (uniformPaddingIncidence R k e) (uniformPaddingIncidence R k f)) :
    ∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Finset.disjoint_left.mp (hM e he f hf hef)
    ((uniformPadding_original_mem R k e v).mpr hv) ((uniformPadding_original_mem R k f v).mpr hw)

end Oberwolfach
