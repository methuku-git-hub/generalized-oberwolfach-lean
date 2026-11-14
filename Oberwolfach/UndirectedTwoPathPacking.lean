module

public import Oberwolfach.TwoPathPacking
public import Mathlib.Data.Sym.Sym2

@[expose] public section

/-! Packing paths for parity switches. Both orientations of every previously
used edge are excluded; directed arc-disjointness alone would not suffice. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def twoPathEdges {V : Type*} [DecidableEq V] (x y z : V) : Finset (Sym2 V) :=
  {s(x,z),s(z,y)}

theorem undirectedTwoPathPacking_next {I V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset I) (x y z : I → V) (u v : V) (C : Finset V)
    (L : ℕ) (hL : 0<L) {a : ℝ}
    (hx : ∀ w,((S.filter (fun i => x i=w)).card:ℝ)≤a)
    (hy : ∀ w,((S.filter (fun i => y i=w)).card:ℝ)≤a)
    (hm : ∀ w,middleCount S z w≤L)
    (hlarge : (S.card:ℝ)/L+4*a+4*L<C.card) :
    ∃ w∈C,middleCount S z w<L ∧
      (u,w)∉packedArcs S x y z ∧ (w,v)∉packedArcs S x y z ∧
      (w,u)∉packedArcs S x y z ∧ (v,w)∉packedArcs S x y z := by
  classical
  let Fu := Finset.univ.filter (fun w => (w,u)∈packedArcs S x y z)
  let Fv := Finset.univ.filter (fun w => (v,w)∈packedArcs S x y z)
  have hFu : (Fu.card:ℝ)≤a+L := by
    have hh := packedArcs_in_bound S x y z u
    have hr : (Fu.card:ℝ)≤((S.filter (fun i => y i=u)).card:ℝ)+middleCount S z u := by
      exact_mod_cast hh
    have hm' : (middleCount S z u:ℝ)≤L := by exact_mod_cast hm u
    linarith [hy u]
  have hFv : (Fv.card:ℝ)≤a+L := by
    have hh := packedArcs_out_bound S x y z v
    have hr : (Fv.card:ℝ)≤((S.filter (fun i => x i=v)).card:ℝ)+middleCount S z v := by
      exact_mod_cast hh
    have hm' : (middleCount S z v:ℝ)≤L := by exact_mod_cast hm v
    linarith [hx v]
  obtain ⟨w,hw,hmw,hu,hv,hwu,hvw⟩ := twoPathPacking_next S x y z u v C Fu Fv L hL
    (hx u) (hy v) hm hFu hFv (by linarith)
  exact ⟨w,hw,hmw,hu,hv,by simpa [Fu] using hwu,by simpa [Fv] using hvw⟩

theorem twoPathEdges_disjoint_of_unused {I V : Type*} [DecidableEq V]
    (S : Finset I) (x y z : I → V) (u v w : V)
    (huw : (u,w)∉packedArcs S x y z) (hwv : (w,v)∉packedArcs S x y z)
    (hwu : (w,u)∉packedArcs S x y z) (hvw : (v,w)∉packedArcs S x y z)
    (j : I) (hj : j∈S) :
    Disjoint (twoPathEdges u v w) (twoPathEdges (x j) (y j) (z j)) := by
  classical
  have h1 : (x j,z j)∈packedArcs S x y z := Finset.mem_biUnion.mpr ⟨j,hj,by simp [twoPathArcs]⟩
  have h2 : (z j,y j)∈packedArcs S x y z := Finset.mem_biUnion.mpr ⟨j,hj,by simp [twoPathArcs]⟩
  apply Finset.disjoint_left.mpr
  intro e he hej
  simp only [twoPathEdges,Finset.mem_insert,Finset.mem_singleton] at he hej
  rcases he with rfl | rfl <;> rcases hej with he | he <;>
    rw [Sym2.eq_iff] at he <;> rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    simp_all

theorem undirectedTwoPathPacking_exists
    {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (x y : I → V) (C : I → Finset V)
    (L : ℕ) (hL : 0 < L) {a : ℝ}
    (hx : ∀ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) ≤ a)
    (hy : ∀ v, ((Finset.univ.filter (fun i => y i = v)).card : ℝ) ≤ a)
    (hlarge : ∀ i, (Fintype.card I : ℝ) / L + 4 * a + 4 * L < (C i).card) :
    ∃ z : I → V,
      (∀ i, z i ∈ C i) ∧
      (∀ i j, i ≠ j → Disjoint (twoPathEdges (x i) (y i) (z i))
        (twoPathEdges (x j) (y j) (z j))) ∧
      ∀ v, middleCount Finset.univ z v ≤ L := by
  classical
  have hall (S : Finset I) : ∃ z : I → V,
      (∀ i ∈ S, z i ∈ C i) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (twoPathEdges (x i) (y i) (z i))
        (twoPathEdges (x j) (y j) (z j))) ∧
      ∀ v, middleCount S z v ≤ L := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => Classical.choice inferInstance, by simp, by simp,
        fun v => by simp [middleCount]⟩
    | @insert i S hi ih =>
      obtain ⟨z, hz, hdisj, hmiddle⟩ := ih
      have hxp (v : V) : ((S.filter (fun j => x j = v)).card : ℝ) ≤ a := by
        apply le_trans _ (hx v)
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ S))
      have hyp (v : V) : ((S.filter (fun j => y j = v)).card : ℝ) ≤ a := by
        apply le_trans _ (hy v)
        exact_mod_cast Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ S))
      have hcp : (S.card : ℝ) / L + 4 * a + 4 * L < (C i).card := by
        have hc : (S.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ S
        have hd := div_le_div_of_nonneg_right hc (Nat.cast_nonneg L)
        linarith [hlarge i]
      obtain ⟨w,hw,hsat,hout,hin,hinrev,houtrev⟩ :=
        undirectedTwoPathPacking_next S x y z (x i) (y i) (C i) L hL hxp hyp hmiddle hcp
      let z' := Function.update z i w
      have heq (j : I) (hj : j ∈ S) : z' j = z j := by
        exact Function.update_of_ne (by intro hji; subst j; exact hi hj) _ _
      have hnew : z' i = w := Function.update_self _ _ _
      have hn (j : I) (hj : j ∈ S) :
          Disjoint (twoPathEdges (x i) (y i) w) (twoPathEdges (x j) (y j) (z j)) := by
        exact twoPathEdges_disjoint_of_unused S x y z (x i) (y i) w hout hin hinrev houtrev j hj
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
        · simpa only [hnew] using hw
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

end Oberwolfach
