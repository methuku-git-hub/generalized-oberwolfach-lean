module

public import Oberwolfach.SequentialChoices
public import Oberwolfach.DenseCommonNeighbourBounds

@[expose] public section

/-! Labelled embeddings of a fixed graph, with one prescribed root.
Every extension is counted after excluding all used vertices and all their
neighbours in the supplied conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Positions `0,1,...,n` are occupied by the root followed by the free labels. -/
def RootedPatternGood {V : Type*} (P F : SimpleGraph V) (A : Finset V)
    (G : SimpleGraph ℕ) (v : V) {n : ℕ} (f : Fin n → V) : Prop :=
  Function.Injective (Fin.cons (α:=fun _=>V) v f) ∧ (∀ i,f i∈A) ∧
  (∀ i j,¬F.Adj (Fin.cons (α:=fun _=>V) v f i) (Fin.cons (α:=fun _=>V) v f j)) ∧
  (∀ i j : Fin (n+1),G.Adj (i:ℕ) (j:ℕ) → P.Adj (Fin.cons (α:=fun _=>V) v f i) (Fin.cons (α:=fun _=>V) v f j))

theorem rootedPatternGood_extend {V : Type*} [DecidableEq V]
    (P F : SimpleGraph V) (A : Finset V) (G : SimpleGraph ℕ) (v : V)
    {n : ℕ} (f : Fin n → V) (hf : RootedPatternGood P F A G v f) (w : V)
    (hw : w∈A) (hne : ∀ i : Fin (n+1),w≠Fin.cons (α:=fun _=>V) v f i)
    (hF : ∀ i : Fin (n+1),¬F.Adj w (Fin.cons (α:=fun _=>V) v f i))
    (hP : ∀ i : Fin (n+1),G.Adj (i:ℕ) (n+1) → P.Adj (Fin.cons (α:=fun _=>V) v f i) w) :
    RootedPatternGood P F A G v (Fin.snoc f w) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [Fin.cons_snoc_eq_snoc_cons]
    apply Fin.snoc_injective_of_injective hf.1
    rintro ⟨i,hi⟩
    exact hne i hi.symm
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.snoc_last] using hw
    · simpa only [Fin.snoc_castSucc] using hf.2.1 j
  · intro i j
    rw [Fin.cons_snoc_eq_snoc_cons]
    refine Fin.lastCases ?_ (fun a=>?_) i
    · refine Fin.lastCases ?_ (fun b=>?_) j
      · simp only [Fin.snoc_last];exact F.loopless.irrefl w
      · simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hF b
    · refine Fin.lastCases ?_ (fun b=>?_) j
      · simp only [Fin.snoc_last,Fin.snoc_castSucc]
        exact fun hh=>hF a hh.symm
      · simpa only [Fin.snoc_castSucc] using hf.2.2.1 a b
  · intro i j
    rw [Fin.cons_snoc_eq_snoc_cons]
    refine Fin.lastCases ?_ (fun a=>?_) i
    · refine Fin.lastCases ?_ (fun b=>?_) j
      · intro hh;exact False.elim (G.loopless.irrefl _ hh)
      · intro hh
        simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hP b hh.symm).symm
    · refine Fin.lastCases ?_ (fun b=>?_) j
      · intro hh
        simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hP a hh
      · intro hh
        simpa only [Fin.snoc_castSucc] using hf.2.2.2 a b hh

theorem rooted_pattern_embedding_count {V : Type*} [Fintype V] [DecidableEq V]
    (P F : SimpleGraph V) (A : Finset V) (G : SimpleGraph ℕ) (v : V)
    (K b : ℕ) (δ L a : ℝ) (hδ : δ≤1) (hL : 0≤L) (ha : 0≤a)
    (hbudget : a≤(1-(b:ℝ)*(1-δ))*(A.card:ℝ)-((K:ℝ)+1)*(L+1))
    (hP : ∀ z∈A∪{v},δ*(A.card:ℝ)≤((A∩P.neighborFinset z).card:ℝ))
    (hF : ∀ z,(F.degree z:ℝ)≤L)
    (hback : ∀ n<K,(Finset.univ.filter (fun i : Fin (n+1)=>G.Adj (i:ℕ) (n+1))).card≤b) :
    a^K≤(Fintype.card {f : Fin K → V // RootedPatternGood P F A G v f}:ℝ) := by
  apply sequential_choices_count (fun _ f=>RootedPatternGood P F A G v f) K a ha
  · intro f
    refine ⟨fun i j _=>by apply Fin.ext;omega,(fun i=>Fin.elim0 i),?_,?_⟩
    · intro i j
      have hi : i=0 := by apply Fin.ext;omega
      have hj : j=0 := by apply Fin.ext;omega
      simpa only [hi,hj,Fin.cons_zero] using F.loopless.irrefl v
    · intro i j hh
      have hi : i=j := by apply Fin.ext;omega
      exact False.elim (G.loopless.irrefl _ (hi ▸ hh))
  · intro n hn f hf
    let g := Fin.cons (α:=fun _=>V) v f
    let S := Finset.univ.image g
    let C := Finset.univ.filter (fun i : Fin (n+1)=>G.Adj (i:ℕ) (n+1))
    let R := C.image g
    let W := common A R (fun z=>P.neighborFinset z)\(S∪S.biUnion (fun z=>F.neighborFinset z))
    have hS : (S.card:ℝ)≤(K:ℝ)+1 := by
      have hc : S.card≤n+1 := (Finset.card_image_le).trans_eq (Fintype.card_fin (n+1))
      have hn' : (n+1:ℕ)≤K+1 := by omega
      exact_mod_cast hc.trans hn'
    have hR : (R.card:ℝ)≤b := by
      exact_mod_cast (Finset.card_image_le.trans (hback n hn) : R.card≤b)
    have hdom : ∀ z∈S,z∈A∪{v} := by
      intro z hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      refine Fin.cases ?_ (fun j=>?_) i
      · simp only [g,Fin.cons_zero,Finset.mem_union,Finset.mem_singleton,or_true]
      · exact Finset.mem_union_left _ (hf.2.1 j)
    have hRS : R⊆S := Finset.image_subset_image (Finset.filter_subset _ _)
    have hlow := dense_common_neighbour_avoiding_used P F A R S δ L
      (fun z hz=>hP z (hdom z (hRS hz))) hF
    have hcount : a≤(W.card:ℝ) := by
      have hb := mul_le_mul_of_nonneg_right hR (show 0≤1-δ by linarith)
      have hb' := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg A.card : (0:ℝ)≤A.card)
      have hs := mul_le_mul_of_nonneg_right hS (show 0≤L+1 by linarith)
      dsimp only [W]
      nlinarith only [hbudget,hlow,hb',hs]
    have hvalid (w : V) (hw : w∈W) : RootedPatternGood P F A G v (Fin.snoc f w) := by
      obtain ⟨hwc,hout⟩ := Finset.mem_sdiff.mp hw
      have hc : w∈A ∧ ∀ z∈R,w∈P.neighborFinset z := by
        simpa only [common,Finset.mem_filter] using hwc
      have hnotS : w∉S := fun hh=>hout (Finset.mem_union_left _ hh)
      have hnotN : w∉S.biUnion (fun z=>F.neighborFinset z) := fun hh=>hout (Finset.mem_union_right _ hh)
      have hg (i : Fin (n+1)) : g i∈S := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      apply rootedPatternGood_extend P F A G v f hf w hc.1
      · intro i he
        exact hnotS (he.symm ▸ hg i)
      · intro i hadj
        exact hnotN (Finset.mem_biUnion.mpr ⟨g i,hg i,(F.mem_neighborFinset (g i) w).mpr hadj.symm⟩)
      · intro i hi
        have hir : g i∈R := Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
        exact (P.mem_neighborFinset (g i) w).mp (hc.2 _ hir)
    let inj : {w : V // w∈W} → {w : V // RootedPatternGood P F A G v (Fin.snoc f w)} :=
      fun w=>⟨w.val,hvalid w.val w.property⟩
    have hinj : Function.Injective inj := by
      intro x y he
      apply Subtype.ext
      exact congrArg (fun z : {w : V // RootedPatternGood P F A G v (Fin.snoc f w)}=>z.val) he
    have hh := Fintype.card_le_of_injective inj hinj
    have hcard : W.card≤Fintype.card {w : V // RootedPatternGood P F A G v (Fin.snoc f w)} := by
      simpa only [Fintype.card_coe] using hh
    exact hcount.trans (by exact_mod_cast hcard)

end Oberwolfach
