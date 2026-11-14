module

public import Oberwolfach.TupleRelationDeletionCounts
public import Oberwolfach.SequentialChoices

@[expose] public section

/-! Counts of actual ordered tuples avoiding previously used labels.
No independence between the successive tuple choices is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tuple_family_avoiding_lower (d : ℕ) (P : (Fin d → V) → Prop) (W : Finset V) :
    (Fintype.card {f // P f}:ℝ)-(d:ℝ)*W.card*(Fintype.card V:ℝ)^(d-1)≤
      Fintype.card {f // P f ∧ ∀ j,f j∉W} := by
  have h := finite_predicate_loss_union P (fun f => P f ∧ ∀ j,f j∉W)
    (fun j : Fin d => fun f => f j∈W) (by
      intro f hp hnot
      have hh : ¬∀ j,f j∉W := fun hh => hnot ⟨hp,hh⟩
      simpa only [not_forall,not_not] using hh)
  have hj (j : Fin d) : (∑ f : Fin d → V,if f j∈W then (1:ℝ) else 0)=
      (W.card:ℝ)*(Fintype.card V:ℝ)^(d-1) := by
    have hh := tuple_unary_indicator_count (fun v : V => v∈W) j
    have hw : (∑ x : V,if x∈W then (1:ℝ) else 0)=(W.card:ℝ) := by
      rw [← Finset.sum_filter]
      simp
    have hh' : (∑ f : Fin d → V,if f j∈W then (1:ℝ) else 0)=
        (∑ x : V,if x∈W then (1:ℝ) else 0)*(Fintype.card V:ℝ)^(d-1) := by
      convert hh using 1 <;> congr! <;> simp
    rw [hw] at hh'
    exact hh'
  have hsum : (∑ j : Fin d,∑ f : Fin d → V,if f j∈W then (1:ℝ) else 0)=
      (d:ℝ)*W.card*(Fintype.card V:ℝ)^(d-1) := by simp only [hj,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  have hh : (Fintype.card {f // P f}:ℝ)-Fintype.card {f // P f ∧ ∀ j,f j∉W}≤
      ∑ j : Fin d,∑ f : Fin d → V,if f j∈W then (1:ℝ) else 0 := by
    convert h using 1 <;> congr!
  rw [hsum] at hh
  linarith

variable {d : ℕ}

def DisjointTupleGood (W : Finset V) (P : ℕ → (Fin d → V) → Prop)
    {n : ℕ} (f : Fin n → (Fin d → V)) : Prop :=
  (∀ i,P i.val (f i)) ∧ (∀ i j,f i j∉W) ∧
    Function.Injective (fun p : Fin n × Fin d => f p.1 p.2)

theorem disjointTupleGood_extend (d : ℕ) (W : Finset V) (P : ℕ → (Fin d → V) → Prop)
    {n : ℕ} (f : Fin n → (Fin d → V)) (hf : DisjointTupleGood W P f)
    (g : Fin d → V) (hg : P n g) (hginj : Function.Injective g)
    (havoid : ∀ j,g j∉W∪Finset.univ.biUnion (fun i => Finset.univ.image (f i))) :
    DisjointTupleGood W P (Fin.snoc f g) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [Fin.snoc_last,Fin.val_last] using hg
    · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hf.1 i
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [Fin.snoc_last] using (fun hj => havoid j (Finset.mem_union_left _ hj))
    · simpa only [Fin.snoc_castSucc] using hf.2.1 i j
  · rintro ⟨i,j⟩ ⟨i',j'⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun i' => ?_) i'
      · intro he
        simp only [Fin.snoc_last] at he
        exact Prod.ext rfl (hginj he)
      · intro he
        simp only [Fin.snoc_last,Fin.snoc_castSucc] at he
        exact False.elim (havoid j (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i',Finset.mem_univ _,Finset.mem_image.mpr ⟨j',Finset.mem_univ _,he.symm⟩⟩)))
    · refine Fin.lastCases ?_ (fun i' => ?_) i'
      · intro he
        simp only [Fin.snoc_last,Fin.snoc_castSucc] at he
        exact False.elim (havoid j' (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he⟩⟩)))
      · intro he
        simp only [Fin.snoc_castSucc] at he
        have hh := hf.2.2 (a₁:=(i,j)) (a₂:=(i',j')) he
        cases hh
        rfl

theorem sequential_disjoint_tuple_count (d K : ℕ) (W : Finset V)
    (P : ℕ → (Fin d → V) → Prop) (M a : ℝ) (ha : 0≤a)
    (hcount : ∀ n<K,M≤Fintype.card {g // P n g})
    (hinj : ∀ n<K,∀ g,P n g → Function.Injective g)
    (hbudget : a+(d:ℝ)*((W.card:ℝ)+K*d)*(Fintype.card V:ℝ)^(d-1)≤M) :
    a^K≤Fintype.card {f : Fin K → (Fin d → V) // DisjointTupleGood W P f} := by
  apply sequential_choices_count (fun _ f => DisjointTupleGood W P f) K a ha
  · intro f
    exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun p => Fin.elim0 p.1⟩
  · intro n hn f hf
    let U := W∪Finset.univ.biUnion (fun i => Finset.univ.image (f i))
    have hU : U.card≤W.card+K*d := by
      apply (Finset.card_union_le _ _).trans
      apply Nat.add_le_add_left
      calc
        _ ≤ ∑ i : Fin n,(Finset.univ.image (f i)).card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin n,d := Finset.sum_le_sum (fun i _ => Finset.card_image_le.trans_eq (Fintype.card_fin d))
        _ = n*d := by simp
        _ ≤ K*d := Nat.mul_le_mul_right _ hn.le
    have hloss := tuple_family_avoiding_lower d (P n) U
    have hUR : (U.card:ℝ)≤(W.card:ℝ)+(K:ℝ)*d := by exact_mod_cast hU
    have hUloss := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hUR (Nat.cast_nonneg d)) (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) (d-1))
    have hlow : a≤Fintype.card {g // P n g ∧ ∀ j,g j∉U} := by linarith [hcount n hn]
    let embed : {g // P n g ∧ ∀ j,g j∉U} → {g // DisjointTupleGood W P (Fin.snoc f g)} :=
      fun g => ⟨g.val,disjointTupleGood_extend d W P f hf g.val g.property.1 (hinj n hn _ g.property.1) g.property.2⟩
    have hi : Function.Injective embed := by
      intro g g' he
      apply Subtype.ext
      exact congrArg (fun z : {g // DisjointTupleGood W P (Fin.snoc f g)} => z.val) he
    have hcard := Fintype.card_le_of_injective embed hi
    exact hlow.trans (by exact_mod_cast hcard)

end Oberwolfach
