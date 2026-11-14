module

public import HadwigerLean.Quantitative.MatchingApplication
public import Mathlib.Tactic

@[expose] public section

/-! Explicit projection between indexed copies of resource sets and a
matching of the original indices. Parallel copies are never identified
until after the matching has been obtained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def copiedResourceHypergraph {V E : Type*} [Fintype V] [Fintype E]
    (R : E → Finset V) (m : E → ℕ) : HadwigerLean.IndexedHypergraph V (Σ e, Fin (m e)) where
  vertices := Finset.univ
  edges := Finset.univ
  edge := fun e => R e.1
  edge_subset := fun _ _ => Finset.subset_univ _

theorem copiedResource_degree {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (m : E → ℕ) (v : V) :
    (copiedResourceHypergraph R m).degree v = ∑ e, if v∈R e then m e else 0 := by
  simp only [HadwigerLean.IndexedHypergraph.degree,copiedResourceHypergraph,
    Finset.card_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : v∈R e <;> simp [h]

theorem copiedResource_codegree {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (m : E → ℕ) (u v : V) :
    (copiedResourceHypergraph R m).codegree u v =
      ∑ e, if u∈R e ∧ v∈R e then m e else 0 := by
  simp only [HadwigerLean.IndexedHypergraph.codegree,copiedResourceHypergraph,
    Finset.card_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : u∈R e ∧ v∈R e <;> simp [h]

theorem copiedResource_matching_projection
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (R : E → Finset V) (m : E → ℕ) (M : Finset (Σ e, Fin (m e)))
    (hM : (copiedResourceHypergraph R m).IsMatching M) :
    (M.image Sigma.fst : Set E).Pairwise (fun e f => Disjoint (R e) (R f)) ∧
    (M.image Sigma.fst).biUnion R=(copiedResourceHypergraph R m).covered M := by
  constructor
  · intro e he f hf hef
    obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f',hf',rfl⟩ := Finset.mem_image.mp hf
    exact hM.2 he' hf' (fun h => hef (congrArg Sigma.fst h))
  · change (M.image Sigma.fst).biUnion R=M.biUnion (fun e => R e.1)
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨e,⟨f,hf,rfl⟩,hv⟩
      exact ⟨f,hf,hv⟩
    · rintro ⟨f,hf,hv⟩
      exact ⟨f.1,⟨f,hf,rfl⟩,hv⟩

theorem sum_floor_scaled_weight_bounds {E : Type*} [Fintype E]
    (w : E → ℝ) (hw : ∀ e, 0≤w e) (P : E → Prop) [DecidablePred P] (T : ℕ) :
    (T : ℝ)*(∑ e, if P e then w e else 0)-Fintype.card E ≤
      ((∑ e, if P e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ) ∧
    ((∑ e, if P e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ) ≤
      (T : ℝ)*(∑ e, if P e then w e else 0) := by
  have hp (e : E) : 0≤(T : ℝ)*w e := mul_nonneg (Nat.cast_nonneg _) (hw e)
  constructor
  · have hh (e : E) : (T : ℝ)*(if P e then w e else 0)-1≤
        ((if P e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ) := by
      by_cases h : P e
      · simp only [h,ite_true]
        have hf := Nat.lt_floor_add_one ((T : ℝ)*w e)
        linarith
      · simp [h]
    have hh' := Finset.sum_le_sum (fun e (_ : e∈Finset.univ) => hh e)
    simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,mul_one,← Nat.cast_sum] using hh'
  · have hh (e : E) : ((if P e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ)≤
        (T : ℝ)*(if P e then w e else 0) := by
      by_cases h : P e
      · simpa only [h,ite_true] using Nat.floor_le (hp e)
      · simp [h]
    have hh' := Finset.sum_le_sum (fun e (_ : e∈Finset.univ) => hh e)
    simpa only [← Finset.mul_sum,← Nat.cast_sum] using hh'

end Oberwolfach
