module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-!
Packing prescribed directed paths of length two. All counts refer to the
original request set, and a middle vertex has a separate capacity.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def twoPathArcs {V : Type*} [DecidableEq V] (x y z : V) : Finset (V × V) :=
  {(x, z), (z, y)}

def packedArcs {I V : Type*} [DecidableEq V]
    (S : Finset I) (x y z : I → V) : Finset (V × V) :=
  S.biUnion (fun i => twoPathArcs (x i) (y i) (z i))

def middleCount {I V : Type*} [DecidableEq V]
    (S : Finset I) (z : I → V) (v : V) : ℕ :=
  (S.filter (fun i => z i = v)).card

theorem middleCount_total
    {I V : Type*} [Fintype V] [DecidableEq V] (S : Finset I) (z : I → V) :
    ∑ v, middleCount S z v = S.card := by
  classical
  unfold middleCount
  simpa using Finset.sum_card_fiberwise_eq_card_filter S Finset.univ z

theorem saturatedMiddles_bound
    {I V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset I) (z : I → V) (L : ℕ) :
    L * (Finset.univ.filter (fun v => L ≤ middleCount S z v)).card ≤ S.card := by
  calc
    _ = ∑ v ∈ Finset.univ.filter (fun v => L ≤ middleCount S z v), L := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => L ≤ middleCount S z v), middleCount S z v :=
      Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
    _ ≤ ∑ v, middleCount S z v := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = S.card := middleCount_total S z

theorem packedArcs_out_bound
    {I V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset I) (x y z : I → V) (v : V) :
    (Finset.univ.filter (fun w => (v, w) ∈ packedArcs S x y z)).card ≤
      (S.filter (fun i => x i = v)).card + middleCount S z v := by
  classical
  have hsub : Finset.univ.filter (fun w => (v, w) ∈ packedArcs S x y z) ⊆
      ((S.filter (fun i => x i = v)).image z) ∪
        ((S.filter (fun i => z i = v)).image y) := by
    intro w hw
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hw).2
    simp only [twoPathArcs, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hp
    rcases hp with ⟨hx, hz⟩ | ⟨hz, hy⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hx.symm⟩, hz.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hz.symm⟩, hy.symm⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)))

theorem packedArcs_in_bound
    {I V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset I) (x y z : I → V) (v : V) :
    (Finset.univ.filter (fun w => (w, v) ∈ packedArcs S x y z)).card ≤
      (S.filter (fun i => y i = v)).card + middleCount S z v := by
  classical
  have hsub : Finset.univ.filter (fun w => (w, v) ∈ packedArcs S x y z) ⊆
      ((S.filter (fun i => y i = v)).image z) ∪
        ((S.filter (fun i => z i = v)).image x) := by
    intro w hw
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hw).2
    simp only [twoPathArcs, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hp
    rcases hp with ⟨hx, hz⟩ | ⟨hz, hy⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hz.symm⟩, hx.symm⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hy.symm⟩, hz.symm⟩)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)))

/-- One next path can be chosen from the fixed candidate set. Already used
arcs, saturated middles and the two forbidden-neighbourhood sets are all
removed by their realised cardinalities. -/
theorem twoPathPacking_next
    {I V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset I) (x y z : I → V) (u v : V) (C : Finset V)
    (Fu Fv : Finset V) (L : ℕ) (hL : 0 < L) {a f : ℝ}
    (hx : ((S.filter (fun i => x i = u)).card : ℝ) ≤ a)
    (hy : ((S.filter (fun i => y i = v)).card : ℝ) ≤ a)
    (hmiddle : ∀ w, middleCount S z w ≤ L)
    (hFu : (Fu.card : ℝ) ≤ f) (hFv : (Fv.card : ℝ) ≤ f)
    (hlarge : (S.card : ℝ) / L + 2 * a + 2 * L + 2 * f < C.card) :
    ∃ w ∈ C, middleCount S z w < L ∧
      (u, w) ∉ packedArcs S x y z ∧ (w, v) ∉ packedArcs S x y z ∧
      w ∉ Fu ∧ w ∉ Fv := by
  classical
  let Sat := Finset.univ.filter (fun w => L ≤ middleCount S z w)
  let Out := Finset.univ.filter (fun w => (u, w) ∈ packedArcs S x y z)
  let In := Finset.univ.filter (fun w => (w, v) ∈ packedArcs S x y z)
  let Bad := (((Sat ∪ Out) ∪ In) ∪ Fu) ∪ Fv
  have hSat : (Sat.card : ℝ) ≤ (S.card : ℝ) / L := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hL)).mpr
    have hh := saturatedMiddles_bound S z L
    exact_mod_cast (by simpa [Sat, Nat.mul_comm] using hh)
  have hOut : (Out.card : ℝ) ≤ a + L := by
    have hh := packedArcs_out_bound S x y z u
    have hm := hmiddle u
    have hr : (Out.card : ℝ) ≤
        ((S.filter (fun i => x i = u)).card : ℝ) + middleCount S z u := by
      exact_mod_cast hh
    have hmr : (middleCount S z u : ℝ) ≤ L := by exact_mod_cast hm
    linarith
  have hIn : (In.card : ℝ) ≤ a + L := by
    have hh := packedArcs_in_bound S x y z v
    have hm := hmiddle v
    have hr : (In.card : ℝ) ≤
        ((S.filter (fun i => y i = v)).card : ℝ) + middleCount S z v := by
      exact_mod_cast hh
    have hmr : (middleCount S z v : ℝ) ≤ L := by exact_mod_cast hm
    linarith
  have hBadNat : Bad.card ≤ Sat.card + Out.card + In.card + Fu.card + Fv.card := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
          (Finset.card_union_le _ _) _)) _)) _)
  have hBad : (Bad.card : ℝ) < C.card := by
    have hh : (Bad.card : ℝ) ≤
        (Sat.card : ℝ) + Out.card + In.card + Fu.card + Fv.card := by
      exact_mod_cast hBadNat
    linarith
  have hnot : ¬ C ⊆ Bad := by
    intro hsub
    have hh : (C.card : ℝ) ≤ Bad.card := by exact_mod_cast Finset.card_le_card hsub
    linarith
  obtain ⟨w, hw, hbad⟩ := Finset.not_subset.mp hnot
  have hh : (((middleCount S z w < L ∧ (u, w) ∉ packedArcs S x y z) ∧
      (w, v) ∉ packedArcs S x y z) ∧ w ∉ Fu) ∧ w ∉ Fv := by
    simpa only [Bad, Sat, Out, In, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or, not_le] using hbad
  exact ⟨w, hw, hh.1.1.1.1, hh.1.1.1.2, hh.1.1.2, hh.1.2, hh.2⟩

/-- Simultaneous packing for a fixed list of endpoint pairs. The same
real endpoint bound is used for every partial packing. -/
theorem twoPathPacking_exists
    {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (x y : I → V) (C : I → Finset V) (F : V → Finset V)
    (L : ℕ) (hL : 0 < L) {a f : ℝ}
    (hx : ∀ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) ≤ a)
    (hy : ∀ v, ((Finset.univ.filter (fun i => y i = v)).card : ℝ) ≤ a)
    (hF : ∀ v, ((F v).card : ℝ) ≤ f)
    (hlarge : ∀ i, (Fintype.card I : ℝ) / L + 2 * a + 2 * L + 2 * f < (C i).card) :
    ∃ z : I → V,
      (∀ i, z i ∈ C i ∧ z i ∉ F (x i) ∧ z i ∉ F (y i)) ∧
      (∀ i j, i ≠ j → Disjoint (twoPathArcs (x i) (y i) (z i))
        (twoPathArcs (x j) (y j) (z j))) ∧
      ∀ v, middleCount Finset.univ z v ≤ L := by
  classical
  have hall (S : Finset I) : ∃ z : I → V,
      (∀ i ∈ S, z i ∈ C i ∧ z i ∉ F (x i) ∧ z i ∉ F (y i)) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (twoPathArcs (x i) (y i) (z i))
        (twoPathArcs (x j) (y j) (z j))) ∧
      ∀ v, middleCount S z v ≤ L := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => Classical.choice inferInstance, by simp, by simp,
        fun v => by simp [middleCount]⟩
    | @insert i S hi ih =>
      obtain ⟨z, hz, hdisj, hmiddle⟩ := ih
      have hxp : ((S.filter (fun j => x j = x i)).card : ℝ) ≤ a := by
        apply le_trans _ (hx (x i))
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ S))
      have hyp : ((S.filter (fun j => y j = y i)).card : ℝ) ≤ a := by
        apply le_trans _ (hy (y i))
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ S))
      have hcp : (S.card : ℝ) / L + 2 * a + 2 * L + 2 * f < (C i).card := by
        have hc : (S.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ S
        have hd := div_le_div_of_nonneg_right hc (Nat.cast_nonneg L)
        linarith [hlarge i]
      obtain ⟨w, hw, hsat, hout, hin, hfu, hfv⟩ :=
        twoPathPacking_next S x y z (x i) (y i) (C i) (F (x i)) (F (y i))
          L hL hxp hyp hmiddle (hF (x i)) (hF (y i)) hcp
      let z' := Function.update z i w
      have heq (j : I) (hj : j ∈ S) : z' j = z j := by
        exact Function.update_of_ne (by intro hji; subst j; exact hi hj) _ _
      have hnew : z' i = w := Function.update_self _ _ _
      have hn (j : I) (hj : j ∈ S) :
          Disjoint (twoPathArcs (x i) (y i) w) (twoPathArcs (x j) (y j) (z j)) := by
        apply Finset.disjoint_left.mpr
        intro e he hej
        have hp : e ∈ packedArcs S x y z := Finset.mem_biUnion.mpr ⟨j, hj, hej⟩
        simp only [twoPathArcs, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with he | he
        · exact hout (he ▸ hp)
        · exact hin (he ▸ hp)
      have hcount (v : V) : middleCount (insert i S) z' v =
          (if w = v then 1 else 0) + middleCount S z v := by
        have hfilter : S.filter (fun j => z' j = v) = S.filter (fun j => z j = v) := by
          apply Finset.filter_congr
          intro j hj
          rw [heq j hj]
        unfold middleCount
        rw [Finset.filter_insert, hfilter, hnew]
        by_cases hwv : w = v <;> simp [hwv, hi, Nat.add_comm]
      refine ⟨z', ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hnew] using And.intro hw (And.intro hfu hfv)
        · simpa only [heq j hj] using hz j hj
      · intro j hj k hk hjk
        by_cases hji : j = i
        · subst j
          have hkS : k ∈ S := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          rw [hnew, heq k hkS]
          exact hn k hkS
        · have hjS : j ∈ S := (Finset.mem_insert.mp hj).resolve_left hji
          by_cases hki : k = i
          · subst k
            rw [heq j hjS, hnew]
            exact (hn j hjS).symm
          · have hkS : k ∈ S := (Finset.mem_insert.mp hk).resolve_left hki
            rw [heq j hjS, heq k hkS]
            exact hdisj j hjS k hkS hjk
      · intro v
        rw [hcount]
        by_cases hwv : w = v
        · subst v
          simp only [ite_true]
          omega
        · simp only [hwv, ite_false, zero_add]
          exact hmiddle v
  obtain ⟨z, hz, hdisj, hmiddle⟩ := hall Finset.univ
  exact ⟨z, fun i => hz i (Finset.mem_univ i),
    fun i j h => hdisj i (Finset.mem_univ i) j (Finset.mem_univ j) h, hmiddle⟩

def twoPathMultiplicity {I V : Type*} [Fintype I] [DecidableEq V]
    (x y z : I → V) (u v : V) : ℕ :=
  (Finset.univ.filter (fun i => (u, v) ∈ twoPathArcs (x i) (y i) (z i))).card

theorem twoPathMultiplicity_le_one
    {I V : Type*} [Fintype I] [DecidableEq V]
    (x y z : I → V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (twoPathArcs (x i) (y i) (z i))
      (twoPathArcs (x j) (y j) (z j))) (u v : V) :
    twoPathMultiplicity x y z u v ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  exact Finset.disjoint_left.mp (hdisj i j hij)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem twoPathMultiplicity_supported
    {I V : Type*} [Fintype I] [DecidableEq V]
    (x y z : I → V) (M : V → V → ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (twoPathArcs (x i) (y i) (z i))
      (twoPathArcs (x j) (y j) (z j)))
    (hpath : ∀ i, 0 < M (x i) (z i) ∧ 0 < M (z i) (y i)) :
    ∀ u v, twoPathMultiplicity x y z u v ≤ M u v := by
  intro u v
  by_cases ht : twoPathMultiplicity x y z u v = 0
  · simp [ht]
  · have hp : 0 < twoPathMultiplicity x y z u v := Nat.pos_of_ne_zero ht
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
    have he := (Finset.mem_filter.mp hi).2
    simp only [twoPathArcs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at he
    have hm : 0 < M u v := by
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hpath i).1
      · exact (hpath i).2
    exact (twoPathMultiplicity_le_one x y z hdisj u v).trans hm

theorem twoPathMultiplicity_degrees
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (x y z : I → V) (hxz : ∀ i, x i ≠ z i) (hzy : ∀ i, z i ≠ y i) :
    (∀ u, (∑ v, twoPathMultiplicity x y z u v) =
      (Finset.univ.filter (fun i => x i = u)).card + middleCount Finset.univ z u) ∧
    (∀ v, (∑ u, twoPathMultiplicity x y z u v) =
      (Finset.univ.filter (fun i => y i = v)).card + middleCount Finset.univ z v) := by
  classical
  have hind (i : I) (u v : V) :
      (if (u, v) ∈ twoPathArcs (x i) (y i) (z i) then 1 else 0 : ℕ) =
      (if u = x i ∧ v = z i then 1 else 0) +
      (if u = z i ∧ v = y i then 1 else 0) := by
    simp only [twoPathArcs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    by_cases h₁ : u = x i ∧ v = z i
    · have h₂ : ¬ (u = z i ∧ v = y i) := by
        rintro ⟨hu, _⟩
        exact hxz i (h₁.1.symm.trans hu)
      simp [h₁, hxz i, hzy i]
    · simp [h₁]
  constructor
  · intro u
    simp only [twoPathMultiplicity, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ((if x i = u then 1 else 0) + (if z i = u then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [hind, Finset.sum_add_distrib]
        by_cases h₁ : u = x i <;> by_cases h₂ : u = z i <;>
          simp [h₁, h₂, eq_comm, hxz i]
      _ = _ := by simp only [middleCount, Finset.card_filter, Finset.sum_add_distrib]
  · intro v
    simp only [twoPathMultiplicity, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ((if y i = v then 1 else 0) + (if z i = v then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [hind, Finset.sum_add_distrib]
        by_cases h₁ : v = z i <;> by_cases h₂ : v = y i <;>
          simp [h₁, h₂, eq_comm, Ne.symm (hzy i)]
      _ = _ := by simp only [middleCount, Finset.card_filter, Finset.sum_add_distrib]

end Oberwolfach
