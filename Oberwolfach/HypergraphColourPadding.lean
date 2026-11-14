module

public import Oberwolfach.HypergraphColourCliques
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-! Finite padding of each resource and each original colour to a supplied
colour degree. Auxiliary edges use one resource and have private filler
colours, so they do not increase codegrees between distinct resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev ColourPaddingVertex {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ) :=
  (v : V) × (c : C) × Fin (s-(hypergraphColourClique R L v c).card)

abbrev PaddedColour {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ) :=
  C ⊕ (ColourPaddingVertex R L s × Fin (l-1))

def paddedResources {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ) :
    E ⊕ ColourPaddingVertex R L s → Finset V
  | .inl e => R e
  | .inr d => {d.1}

def paddedColourList {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ) :
    E ⊕ ColourPaddingVertex R L s → Finset (PaddedColour R L s l)
  | .inl e => (L e).map Function.Embedding.inl
  | .inr d => {Sum.inl d.2.1} ∪ Finset.univ.map
      ⟨fun i=>Sum.inr (d,i),fun _ _ h=>Prod.mk.inj (Sum.inr.inj h) |>.2⟩

theorem paddedColourList_original {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (e : E ⊕ ColourPaddingVertex R L s) (c : C) :
    Sum.inl c∈paddedColourList R L s l e ↔
      match e with
      | .inl f => c∈L f
      | .inr d => c=d.2.1 := by
  cases e <;> simp [paddedColourList]

theorem paddedColourList_private {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (e : E ⊕ ColourPaddingVertex R L s)
    (d : ColourPaddingVertex R L s) (i : Fin (l-1)) :
    Sum.inr (d,i)∈paddedColourList R L s l e ↔ e=Sum.inr d := by
  cases e <;> simp [paddedColourList]

theorem paddedColourList_card {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ)
    {l : ℕ} (hl : 0<l) (hcard : ∀ e,(L e).card=l)
    (e : E ⊕ ColourPaddingVertex R L s) : (paddedColourList R L s l e).card=l := by
  classical
  cases e with
  | inl e => simpa only [paddedColourList,Finset.card_map] using hcard e
  | inr d =>
    have hd : Disjoint ({Sum.inl d.2.1} : Finset (PaddedColour R L s l))
        (Finset.univ.map ⟨fun i : Fin (l-1)=>Sum.inr (d,i),
          fun _ _ h=>Prod.mk.inj (Sum.inr.inj h) |>.2⟩) := by simp
    rw [paddedColourList,Finset.card_union_of_disjoint hd]
    simp only [Finset.card_singleton,Finset.card_map,Finset.card_univ,Fintype.card_fin]
    omega

theorem paddedResources_size {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ)
    {k : ℕ} (hk : 1≤k) (hsize : ∀ e,(R e).card≤k)
    (e : E ⊕ ColourPaddingVertex R L s) : (paddedResources R L s e).card≤k := by
  cases e with
  | inl e => exact hsize e
  | inr d => simpa only [paddedResources,Finset.card_singleton] using hk

theorem paddedColourClique_card_original
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s)
    (v : V) (c : C) :
    (hypergraphColourClique (paddedResources R L s) (paddedColourList R L s l) v (Sum.inl c)).card=s := by
  classical
  have hpad : (∑ d : ColourPaddingVertex R L s,if v=d.1 ∧ c=d.2.1 then (1 : ℕ) else 0)=
      s-(hypergraphColourClique R L v c).card := by
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_sigma]
    change (∑ v' : V,∑ c' : C,∑ _i : Fin (s-(hypergraphColourClique R L v' c').card),
      if v=v' ∧ c=c' then (1 : ℕ) else 0)=_
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      mul_ite,mul_one,mul_zero,ite_and]
    simp [eq_comm]
  have he :
      (hypergraphColourClique (paddedResources R L s) (paddedColourList R L s l) v (Sum.inl c)).card=
      (hypergraphColourClique R L v c).card+(s-(hypergraphColourClique R L v c).card) := by
    have hset : hypergraphColourClique (paddedResources R L s) (paddedColourList R L s l) v (Sum.inl c)=
        Finset.univ.filter (fun e=>v∈paddedResources R L s e ∧ Sum.inl c∈paddedColourList R L s l e) := by
      ext e
      simp only [hypergraphColourClique,Finset.mem_filter]
    rw [hset]
    conv_lhs => rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    simp only [paddedColourList_original,paddedResources,Finset.mem_singleton]
    rw [hpad]
    congr 1
    simp only [hypergraphColourClique,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [he]
  exact Nat.add_sub_of_le (hdegree v c)

theorem paddedColourClique_card_private
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (v : V) (d : ColourPaddingVertex R L s) (i : Fin (l-1)) :
    (hypergraphColourClique (paddedResources R L s) (paddedColourList R L s l) v (Sum.inr (d,i))).card≤1 := by
  classical
  apply (Finset.card_le_card (show
    hypergraphColourClique (paddedResources R L s) (paddedColourList R L s l) v (Sum.inr (d,i))⊆
      {Sum.inr d} from ?_)).trans (by simp)
  intro e he
  have hm : Sum.inr (d,i)∈paddedColourList R L s l e := by
    have hmem : v∈paddedResources R L s e ∧ Sum.inr (d,i)∈paddedColourList R L s l e := by
      simpa only [hypergraphColourClique,Finset.mem_filter,Finset.mem_univ,true_and] using he
    exact hmem.2
  exact Finset.mem_singleton.mpr ((paddedColourList_private R L s l e d i).mp hm)

theorem paddedColourClique_degree_bound
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) {s : ℕ} (hs : 1≤s) (l : ℕ)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s)
    (v : V) (c : PaddedColour R L s l) :
    (hypergraphColourClique (paddedResources R L s) (paddedColourList R L s l) v c).card≤s := by
  cases c with
  | inl c => exact le_of_eq (paddedColourClique_card_original R L s l hdegree v c)
  | inr p => exact (paddedColourClique_card_private R L s l v p.1 p.2).trans hs

theorem paddedResources_codegree
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ)
    (v w : V) (hvw : v≠w) :
    (Finset.univ.filter (fun e=>v∈paddedResources R L s e ∧ w∈paddedResources R L s e)).card=
      (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  have hz (d : ColourPaddingVertex R L s) :
      ¬(v∈paddedResources R L s (Sum.inr d) ∧ w∈paddedResources R L s (Sum.inr d)) := by
    simpa only [paddedResources,Finset.mem_singleton] using
      (show ¬(v=d.1 ∧ w=d.1) from fun h=>hvw (h.1.trans h.2.symm))
  simp only [hz,ite_false,Finset.sum_const_zero,add_zero]
  rfl

theorem paddedResources_degree_formula
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ) (v : V) :
    (hypergraphVertexClique (paddedResources R L s) v).card=
      (hypergraphVertexClique R v).card+∑ c : C,(s-(hypergraphColourClique R L v c).card) := by
  classical
  have hpad : (∑ d : ColourPaddingVertex R L s,if v=d.1 then (1 : ℕ) else 0)=
      ∑ c : C,(s-(hypergraphColourClique R L v c).card) := by
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_sigma]
    change (∑ v' : V,∑ c' : C,∑ _i : Fin (s-(hypergraphColourClique R L v' c').card),
      if v=v' then (1 : ℕ) else 0)=_
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      mul_ite,mul_one,mul_zero]
    simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
  unfold hypergraphVertexClique
  conv_lhs => rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sum_type]
  simp only [paddedResources,Finset.mem_singleton]
  rw [hpad]
  congr 1
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]

theorem paddedResources_degree_bound
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ) {D : ℕ}
    (hdegree : ∀ v,(hypergraphVertexClique R v).card≤D) (v : V) :
    (hypergraphVertexClique (paddedResources R L s) v).card≤D+Fintype.card C*s := by
  rw [paddedResources_degree_formula]
  apply add_le_add (hdegree v)
  calc
    _ ≤ ∑ _c : C,s := Finset.sum_le_sum (fun c _=>Nat.sub_le _ _)
    _ = _ := by simp

theorem paddedLineGraph_degree_bound
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s : ℕ) {k D : ℕ}
    (hk : 1≤k) (hsize : ∀ e,(R e).card≤k)
    (hdegree : ∀ v,(hypergraphVertexClique R v).card≤D)
    (e : E ⊕ ColourPaddingVertex R L s) :
    (Finset.univ.filter (fun f=>(hypergraphLineGraph (paddedResources R L s)).Adj e f)).card≤
      k*(D+Fintype.card C*s) := by
  classical
  exact hypergraphLineGraph_degree_bound (paddedResources R L s)
    (paddedResources_size R L s hk hsize) (paddedResources_degree_bound R L s hdegree) e

theorem paddedLineGraph_original_adj
    {V E C : Type*} [Fintype E] (R : E → Finset V) (L : E → Finset C) (s : ℕ)
    (e f : E) : (hypergraphLineGraph (paddedResources R L s)).Adj (Sum.inl e) (Sum.inl f) ↔
      (hypergraphLineGraph R).Adj e f := by
  simp only [hypergraphLineGraph,paddedResources,ne_eq,Sum.inl.injEq]

end Oberwolfach
