module

public import Oberwolfach.PermutedNeighbourChoices
public import Oberwolfach.SequentialChoices
public import Oberwolfach.TwistedTupleEdges

@[expose] public section

/-! Greedy labelled sequences with different target classes and physical
head maps at different positions. The neighbour constraints can use any
previous labels or fixed ambient roots. Root labels need not be separated
from one another. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def greedyPrefix {V : Type*} {n : ℕ} (f : Fin n→V) (i : Fin n) : Fin i.val→V :=
  fun j=>f ⟨j.val,lt_trans j.isLt i.isLt⟩

theorem greedyPrefix_snoc_castSucc {V : Type*} {n : ℕ} (f : Fin n→V) (v : V) (i : Fin n) :
    greedyPrefix (Fin.snoc f v) i.castSucc=greedyPrefix f i := by
  funext j
  exact Fin.snoc_castSucc (α:=fun _=>V) v f ⟨j.val,lt_trans j.isLt i.isLt⟩

theorem greedyPrefix_snoc_last {V : Type*} {n : ℕ} (f : Fin n→V) (v : V) :
    greedyPrefix (Fin.snoc f v) (Fin.last n)=f := by
  funext j
  exact Fin.snoc_castSucc (α:=fun _=>V) v f j

def MixedGreedyGood {V : Type*} (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (A : ℕ→Finset V) (τ : ℕ→Equiv.Perm V) (R : ∀ n : ℕ,(Fin n→V)→Finset V)
    (roots : Finset V) {n : ℕ} (f : Fin n→V) : Prop :=
  (∀ i,f i∈A i.val) ∧ PermutationSeparated π b f ∧
  (∀ i,∀ x∈roots,¬PermutationClose π b x (f i)) ∧
  ∀ i,∀ x∈R i.val (greedyPrefix f i),P.Adj x (τ i.val (f i))

theorem mixedGreedyGood_extend {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (A : ℕ→Finset V) (τ : ℕ→Equiv.Perm V) (R : ∀ n : ℕ,(Fin n→V)→Finset V)
    (roots : Finset V) {n : ℕ} (f : Fin n→V)
    (hf : MixedGreedyGood P π b A τ R roots f) (v : V)
    (hv : v∈permutedNeighbourChoices P π (τ n) b (A n) (R n f) (roots∪Finset.univ.image f)) :
    MixedGreedyGood P π b A τ R roots (Fin.snoc f v) := by
  have hv' : v∈A n ∧ (∀ x∈R n f,P.Adj x (τ n v)) ∧
      ∀ x∈roots∪Finset.univ.image f,¬PermutationClose π b x v := by
    simpa only [permutedNeighbourChoices,Finset.mem_filter] using hv
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.snoc_last,Fin.val_last] using hv'.1
    · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hf.1 j
  · intro i
    refine Fin.lastCases ?_ (fun a=>?_) i
    · intro j
      refine Fin.lastCases ?_ (fun c=>?_) j
      · intro hij;exact (hij rfl).elim
      · intro _
        simp only [Fin.snoc_last,Fin.snoc_castSucc]
        rw [permutationClose_symm]
        exact hv'.2.2 (f c) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩))
    · intro j
      refine Fin.lastCases ?_ (fun c=>?_) j
      · intro _
        simpa only [Fin.snoc_last,Fin.snoc_castSucc] using
          hv'.2.2 (f a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
      · intro hij
        simp only [Fin.snoc_castSucc]
        exact hf.2.1 a c (fun he=>hij (congrArg Fin.castSucc he))
  · intro i x hx
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.snoc_last,Fin.val_last] using hv'.2.2 x (Finset.mem_union_left _ hx)
    · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hf.2.2.1 j x hx
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.snoc_last,greedyPrefix_snoc_last,Fin.val_last] using hv'.2.1
    · simpa only [Fin.snoc_castSucc,greedyPrefix_snoc_castSucc,Fin.val_castSucc] using hf.2.2.2 j

theorem mixedGreedyGood_injective {V : Type*}
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (A : ℕ→Finset V) (τ : ℕ→Equiv.Perm V) (R : ∀ n : ℕ,(Fin n→V)→Finset V)
    (roots : Finset V) {n : ℕ} (f : Fin n→V) (hf : MixedGreedyGood P π b A τ R roots f) :
    Function.Injective f := by
  intro i j he
  by_contra hij
  exact hf.2.1 i j hij (Or.inl he)

theorem mixed_greedy_sequence_count {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (A : ℕ→Finset V) (τ : ℕ→Equiv.Perm V) (R : ∀ n : ℕ,(Fin n→V)→Finset V)
    (roots : Finset V) (K : ℕ) (α a : ℝ) (hα1 : α≤1) (ha : 0≤a)
    (hbudget : ∀ n<K,a≤α*(A n).card-((roots.card:ℝ)+K)*(2*(b:ℝ)+1))
    (hdegree : ∀ n<K,∀ x : V,(1/2+α/2)*(A n).card≤
      ((P.neighborFinset x∩(A n).image (τ n)).card:ℝ))
    (hback : ∀ n<K,∀ f : Fin n→V,MixedGreedyGood P π b A τ R roots f → (R n f).card≤2) :
    a^K≤(Fintype.card {f : Fin K→V // MixedGreedyGood P π b A τ R roots f}:ℝ) := by
  apply sequential_choices_count (fun _ f=>MixedGreedyGood P π b A τ R roots f) K a ha
  · intro f
    exact ⟨(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i)⟩
  · intro n hn f hf
    let S := roots∪Finset.univ.image f
    let W := permutedNeighbourChoices P π (τ n) b (A n) (R n f) S
    have hS : (S.card:ℝ)≤(roots.card:ℝ)+K := by
      have hh : S.card≤roots.card+n :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left
          (Finset.card_image_le.trans_eq (Fintype.card_fin n)) _)
      have hh' : S.card≤roots.card+K := hh.trans (Nat.add_le_add_left (by omega) _)
      exact_mod_cast hh'
    have hh := permutedNeighbourChoices_card_lower P π (τ n) b (A n) (R n f) S α hα1
      (hback n hn f hf) (fun x _=>hdegree n hn x)
    have hcount : a≤(W.card:ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hS (show 0≤2*(b:ℝ)+1 by positivity)
      linarith only [hh,hm,hbudget n hn]
    let inj : {v : V // v∈W}→{v : V // MixedGreedyGood P π b A τ R roots (Fin.snoc f v)} :=
      fun v=>⟨v.val,mixedGreedyGood_extend P π b A τ R roots f hf v.val v.property⟩
    have hinj : Function.Injective inj := by
      intro x y he
      apply Subtype.ext
      exact congrArg (fun z : {v : V // MixedGreedyGood P π b A τ R roots (Fin.snoc f v)}=>z.val) he
    have hcard := Fintype.card_le_of_injective inj hinj
    have hcard' : W.card≤Fintype.card {v : V // MixedGreedyGood P π b A τ R roots (Fin.snoc f v)} := by
      simpa only [Fintype.card_coe] using hcard
    exact hcount.trans (by exact_mod_cast hcard')

end Oberwolfach
