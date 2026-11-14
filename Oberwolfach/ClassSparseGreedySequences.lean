module

public import Oberwolfach.MixedGreedySequences
public import Oberwolfach.DenseCommonNeighbourBounds

@[expose] public section

/-! Greedy graph embeddings with a prescribed class at each position.
No minimum-degree hypothesis is imposed on the sparse graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def ClassSparseGreedyGood (Q F : SimpleGraph V) (A : ℕ → Finset V) (W : Finset V)
    (R : ∀ n : ℕ,(Fin n→V)→Finset V) {n : ℕ} (f : Fin n→V) : Prop :=
  Function.Injective f ∧ (∀ i,f i∈A i.val ∧ f i∉W) ∧
  (∀ i j,¬F.Adj (f i) (f j)) ∧ (∀ i,∀ x∈W,¬F.Adj (f i) x) ∧
  ∀ i,∀ x∈R i.val (greedyPrefix f i),Q.Adj x (f i)

theorem classSparseGreedyGood_extend (Q F : SimpleGraph V) (A : ℕ → Finset V) (W : Finset V)
    (R : ∀ n : ℕ,(Fin n→V)→Finset V) {n : ℕ} (f : Fin n→V)
    (hf : ClassSparseGreedyGood Q F A W R f) (v : V)
    (hv : v∈common (A n) (R n f) (fun x=>Q.neighborFinset x)\
      ((W∪Finset.univ.image f)∪(W∪Finset.univ.image f).biUnion (fun x=>F.neighborFinset x))) :
    ClassSparseGreedyGood Q F A W R (Fin.snoc f v) := by
  obtain ⟨hc,hn⟩ := Finset.mem_sdiff.mp hv
  have hc' : v∈A n ∧ ∀ x∈R n f,Q.Adj x v := by
    simpa only [common,Finset.mem_filter,SimpleGraph.mem_neighborFinset] using hc
  have hneq (x : V) (hx : x∈W∪Finset.univ.image f) : v≠x := by
    intro he;exact hn (Finset.mem_union_left _ (he.symm ▸ hx))
  have hconf (x : V) (hx : x∈W∪Finset.univ.image f) : ¬F.Adj v x := by
    intro h;exact hn (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x,hx,(F.mem_neighborFinset x v).mpr h.symm⟩))
  have hused (i : Fin n) : f i∈W∪Finset.univ.image f :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  refine ⟨Fin.snoc_injective_of_injective hf.1 (by rintro ⟨i,hi⟩;exact hneq _ (hused i) hi.symm),?_,?_,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [Fin.snoc_last,Fin.val_last]
      exact ⟨hc'.1,fun hh=>hneq v (Finset.mem_union_left _ hh) rfl⟩
    · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hf.2.1 j
  · intro i j
    refine Fin.lastCases ?_ (fun a=>?_) i
    · refine Fin.lastCases ?_ (fun b=>?_) j
      · simpa only [Fin.snoc_last] using F.loopless.irrefl v
      · simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hconf _ (hused b)
    · refine Fin.lastCases ?_ (fun b=>?_) j
      · simp only [Fin.snoc_last,Fin.snoc_castSucc];exact fun h=>hconf _ (hused a) h.symm
      · simpa only [Fin.snoc_castSucc] using hf.2.2.1 a b
  · intro i x hx
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.snoc_last] using hconf x (Finset.mem_union_left _ hx)
    · simpa only [Fin.snoc_castSucc] using hf.2.2.2.1 j x hx
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.snoc_last,greedyPrefix_snoc_last,Fin.val_last] using hc'.2
    · simpa only [Fin.snoc_castSucc,greedyPrefix_snoc_castSucc,Fin.val_castSucc] using hf.2.2.2.2 j

theorem class_sparse_greedy_sequence_count (Q F : SimpleGraph V) (A : ℕ → Finset V) (W : Finset V)
    (R : ∀ n : ℕ,(Fin n→V)→Finset V) (K : ℕ) (L b a : ℝ)
    (hL : 0≤L) (ha : 0≤a) (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hbudget : a≤b-((W.card:ℝ)+K)*(L+1))
    (hcommon : ∀ n<K,∀ f : Fin n→V,ClassSparseGreedyGood Q F A W R f →
      b≤((common (A n) (R n f) (fun x=>Q.neighborFinset x)).card:ℝ)) :
    a^K≤(Fintype.card {f : Fin K→V // ClassSparseGreedyGood Q F A W R f}:ℝ) := by
  apply sequential_choices_count (fun _ f=>ClassSparseGreedyGood Q F A W R f) K a ha
  · intro f
    exact ⟨(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i),(fun i=>Fin.elim0 i)⟩
  · intro n hn f hf
    let S := W∪Finset.univ.image f
    let C := common (A n) (R n f) (fun x=>Q.neighborFinset x)
    let D := S∪S.biUnion (fun x=>F.neighborFinset x)
    have hS : (S.card:ℝ)≤(W.card:ℝ)+K := by
      have h : S.card≤W.card+n := (Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_image_le.trans_eq (Fintype.card_fin n)) _)
      exact_mod_cast h.trans (Nat.add_le_add_left (Nat.le_of_lt hn) _)
    have hd := forbidden_used_neighbours_card F S L hF
    have hcd : (C.card:ℝ)≤(C\D).card+D.card := by exact_mod_cast
      (Finset.card_le_card_sdiff_add_card (s:=C) (t:=D))
    have hcount : a≤((C\D).card:ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hS (show 0≤L+1 by linarith)
      linarith [hcommon n hn f hf]
    let inj : {v : V // v∈C\D}→{v : V // ClassSparseGreedyGood Q F A W R (Fin.snoc f v)} :=
      fun v=>⟨v.val,classSparseGreedyGood_extend Q F A W R f hf v.val v.property⟩
    have hinj : Function.Injective inj := fun x y h=>Subtype.ext
      (congrArg (fun z : {v : V // ClassSparseGreedyGood Q F A W R (Fin.snoc f v)}=>z.val) h)
    have hh := Fintype.card_le_of_injective inj hinj
    have hh' : (C\D).card≤Fintype.card {v : V // ClassSparseGreedyGood Q F A W R (Fin.snoc f v)} := by
      simpa only [Fintype.card_coe] using hh
    exact hcount.trans (by exact_mod_cast hh')

end Oberwolfach
