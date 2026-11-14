module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Paths of a prescribed fixed length with forbidden vertices. This is
an actual simple path, with every vertex distinct, rather than a walk
whose internal vertices might be repeated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem greedy_simple_path_avoiding (G : SimpleGraph V) (S : Finset V) (x : V) (k : ℕ)
    (hx : x∉S) (hdeg : ∀ v,S.card+k < G.degree v) :
    ∃ z, ∃ p : G.Walk x z, p.IsPath ∧ p.length=k ∧ ∀ v∈p.support,v∉S := by
  induction k with
  | zero => exact ⟨x,SimpleGraph.Walk.nil,by simp,by simp,by simpa using hx⟩
  | succ k ih =>
    obtain ⟨z,p,hp,hplen,havoid⟩ := ih (fun v => by have hh:=hdeg v;omega)
    have hsupport : p.support.toFinset.card ≤ k+1 := by
      exact (List.toFinset_card_le _).trans_eq (by rw [p.length_support,hplen])
    have hsize : (S∪p.support.toFinset).card < (G.neighborFinset z).card := by
      have hh := Finset.card_union_le S p.support.toFinset
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have hd := hdeg z
      omega
    obtain ⟨w,hw,hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
    have hwS : w∉S := fun h => hout (Finset.mem_union_left _ h)
    have hwp : w∉p.support := fun h => hout (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
    have hzw : G.Adj z w := by simpa only [SimpleGraph.mem_neighborFinset] using hw
    refine ⟨w,p.concat hzw,hp.concat hwp hzw,by simpa [hplen],?_⟩
    intro v hv
    rw [SimpleGraph.Walk.support_concat] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact havoid v hv
    · have he : v=w := List.mem_singleton.mp hv
      simpa only [he] using hwS

theorem dense_common_neighbours (G : SimpleGraph V) (n : ℕ) (β : ℝ)
    (hcard : Fintype.card V ≤ n)
    (hdeg : ∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) (x y : V) :
    2*β*n ≤ ((G.neighborFinset x∩G.neighborFinset y).card:ℝ) := by
  have hcardunion : (G.neighborFinset x∪G.neighborFinset y).card ≤ n :=
    (Finset.card_le_univ _).trans hcard
  have hid := Finset.card_inter_add_card_union (G.neighborFinset x) (G.neighborFinset y)
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hid
  have hidR : ((G.neighborFinset x∩G.neighborFinset y).card:ℝ)+
      ((G.neighborFinset x∪G.neighborFinset y).card:ℝ)=(G.degree x:ℝ)+(G.degree y:ℝ) := by exact_mod_cast hid
  have hbound : ((G.neighborFinset x∪G.neighborFinset y).card:ℝ) ≤ n := by exact_mod_cast hcardunion
  linarith [hdeg x,hdeg y]

theorem fixed_length_path_finite (G : SimpleGraph V) (S : Finset V) (x y : V)
    (k : ℕ) (hk : 2 ≤ k) (hxy : x≠y) (hx : x∉S) (hy : y∉S)
    (hdeg : ∀ v,S.card+k < G.degree v)
    (hcommon : ∀ z,S.card+k < (G.neighborFinset z∩G.neighborFinset y).card) :
    ∃ p : G.Walk x y,p.IsPath ∧ p.length=k ∧ ∀ v∈p.support,v∉S := by
  obtain ⟨z,p,hp,hplen,havoid⟩ := greedy_simple_path_avoiding G (insert y S) x (k-2)
    (by simp [hxy,hx]) (by
      intro v
      have hc := Finset.card_insert_le y S
      have hd := hdeg v
      omega)
  have hsupport : p.support.toFinset.card ≤ k-1 := by
    have hh := List.toFinset_card_le p.support
    rw [p.length_support,hplen] at hh
    omega
  have hsize : (S∪p.support.toFinset).card < (G.neighborFinset z∩G.neighborFinset y).card := by
    have hh := Finset.card_union_le S p.support.toFinset
    have hc := hcommon z
    omega
  obtain ⟨w,hw,hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  have hwS : w∉S := fun h => hout (Finset.mem_union_left _ h)
  have hwp : w∉p.support := fun h => hout (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
  have hzw : G.Adj z w := by simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hw).1
  have hyw : G.Adj y w := by simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hw).2
  have hyp : y∉(p.concat hzw).support := by
    rw [SimpleGraph.Walk.support_concat]
    intro hh
    rcases List.mem_append.mp hh with hh | hh
    · exact havoid y hh (Finset.mem_insert_self _ _)
    · exact hyw.ne (List.mem_singleton.mp hh)
  refine ⟨(p.concat hzw).concat hyw.symm,(hp.concat hwp hzw).concat hyp hyw.symm,?_,?_⟩
  · simp only [SimpleGraph.Walk.length_concat,hplen];omega
  · intro v hv
    simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hv
    rcases hv with (hv|hv)|hv
    · exact fun h => havoid v hv (Finset.mem_insert_of_mem h)
    · simpa only [hv] using hwS
    · simpa only [hv] using hy

theorem fixed_length_path (β : ℝ) (hβ : 0 < β) (k b : ℕ) (hk : 2 ≤ k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (V : Type*) [Fintype V] [DecidableEq V], Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V), (∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) →
    ∀ (x y : V), x≠y → ∀ S : Finset V, S.card ≤ b → x∉S → y∉S →
    ∃ p : G.Walk x y,p.IsPath ∧ p.length=k ∧ ∀ v∈p.support,v∉S := by
  let n₀ := Nat.ceil (((b:ℝ)+k+1)/β)+1
  refine ⟨n₀,?_⟩
  intro n hn V _ _ hcard G hdeg x y hxy S hS hx hy
  have hceil : (Nat.ceil (((b:ℝ)+k+1)/β):ℝ) < n := by
    exact_mod_cast (show Nat.ceil (((b:ℝ)+k+1)/β) < n by dsimp [n₀] at hn;omega)
  have hmargin : (b:ℝ)+k+1 < (n:ℝ)*β :=
    (div_lt_iff₀ hβ).mp ((Nat.le_ceil (((b:ℝ)+k+1)/β)).trans_lt hceil)
  have hSR : (S.card:ℝ) ≤ b := by exact_mod_cast hS
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  apply fixed_length_path_finite G S x y k hk hxy hx hy
  · intro v
    have hh := hdeg v
    have hgt : (S.card:ℝ)+k < G.degree v := by nlinarith
    exact_mod_cast hgt
  · intro z
    have hh := dense_common_neighbours G n β hcard hdeg z y
    have hgt : (S.card:ℝ)+k < ((G.neighborFinset z∩G.neighborFinset y).card:ℝ) := by nlinarith
    exact_mod_cast hgt

end Oberwolfach
