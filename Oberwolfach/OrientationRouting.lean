module

public import Oberwolfach.TwoPathPacking
public import Oberwolfach.DegreeRequests
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-!
Degree correction by reversing edge-disjoint directed two-edge paths.
An orientation is encoded by its zero-one directed incidence matrix.
The underlying physical graph is preserved pointwise.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def reversedMultiplicity {V : Type*} (M T : V → V → ℕ) (x y : V) : ℕ :=
  M x y - T x y + T y x

theorem reversedMultiplicity_underlying
    {V : Type*} (M T : V → V → ℕ) (hT : ∀ x y, T x y ≤ M x y) (x y : V) :
    reversedMultiplicity M T x y + reversedMultiplicity M T y x = M x y + M y x := by
  have hxy := hT x y
  have hyx := hT y x
  unfold reversedMultiplicity
  omega

theorem reversedMultiplicity_outdegree
    {V : Type*} [Fintype V] (M T : V → V → ℕ)
    (hT : ∀ x y, T x y ≤ M x y) (x : V) :
    (∑ y, reversedMultiplicity M T x y) + (∑ y, T x y) =
      (∑ y, M x y) + (∑ y, T y x) := by
  simp only [reversedMultiplicity, Finset.sum_add_distrib]
  rw [Finset.sum_tsub_distrib Finset.univ (fun y _ => hT x y)]
  have hh : ∑ y, T x y ≤ ∑ y, M x y := Finset.sum_le_sum (fun y _ => hT x y)
  omega

theorem reversedMultiplicity_changed_degree
    {V : Type*} [Fintype V] (M T : V → V → ℕ) (x : V) :
    (Finset.univ.filter (fun y => reversedMultiplicity M T x y ≠ M x y ∨
      reversedMultiplicity M T y x ≠ M y x)).card ≤
      (∑ y, T x y) + (∑ y, T y x) := by
  classical
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  split_ifs with h
  · by_contra hn
    have ht : T x y = 0 ∧ T y x = 0 := by omega
    simp [reversedMultiplicity, ht.1, ht.2] at h
  · exact Nat.zero_le _

theorem orientationMatrix_total
    {V : Type*} [Fintype V] (G : SimpleGraph V) (M : V → V → ℕ)
    (hphysical : ∀ x y, M x y + M y x = if G.Adj x y then 1 else 0) :
    ∑ x, ∑ y, M x y = G.edgeFinset.card := by
  classical
  have hdegree (x : V) : G.degree x = ∑ y, (M x y + M y x) := by
    rw [SimpleGraph.degree]
    have heq : G.neighborFinset x = Finset.univ.filter (G.Adj x) := by
      ext y
      simp
    rw [heq, Finset.card_filter]
    simp only [hphysical]
  have hh := G.sum_degrees_eq_twice_card_edges
  simp only [hdegree, Finset.sum_add_distrib] at hh
  have hswap : (∑ x, ∑ y, M y x) = ∑ x, ∑ y, M x y := Finset.sum_comm
  rw [hswap] at hh
  omega

/-- The orientation-routing lemma, retaining its real error parameters,
the forbidden graph and the original eligible two-step paths. The output
matrix represents an orientation because the physical-edge equality is
preserved. Its changed-edge degree is measured on the physical vertices. -/
theorem orientationRouting
    {V : Type*} [Fintype V] [DecidableEq V]
    (G E F : SimpleGraph V) (M : V → V → ℕ) (t : V → ℕ)
    (L : ℕ) (hL : 0 < L) (hn : 0 < Fintype.card V)
    {a f β : ℝ} (ha : 0 ≤ a) (_hf : 0 ≤ f) (_hβ : 0 < β)
    (hphysical : ∀ x y, M x y + M y x = if G.Adj x y then 1 else 0)
    (htotal : ∑ v, t v = G.edgeFinset.card)
    (herr : ∀ v, |((∑ w, M v w : ℕ) : ℝ) - t v| ≤ a)
    (hforbid : ∀ v, (F.degree v : ℝ) ≤ f)
    (hpaths : ∀ x y, x ≠ y →
      β * Fintype.card V ≤
        ((Finset.univ.filter (fun z => 0 < M x z ∧ 0 < M z y ∧
          E.Adj x z ∧ E.Adj z y)).card : ℝ))
    (hmargin : (Fintype.card V : ℝ) * a / L + 2 * a + 4 * L + 2 * f <
      β * Fintype.card V) :
    ∃ N : V → V → ℕ,
      (∀ x y, N x y + N y x = if G.Adj x y then 1 else 0) ∧
      (∀ v, ∑ w, N v w = t v) ∧
      (∀ x y, N x y ≠ M x y ∨ N y x ≠ M y x → E.Adj x y ∧ ¬ F.Adj x y) ∧
      ∀ x, ((Finset.univ.filter (fun y => N x y ≠ M x y ∨ N y x ≠ M y x)).card : ℝ) ≤
        a + 2 * L := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp hn
  let d (v : V) := ∑ w, M v w
  have hdtotal : ∑ v, d v = ∑ v, t v :=
    (orientationMatrix_total G M hphysical).trans htotal.symm
  obtain ⟨m, x, y, hm, hx, hy, hends, hxy⟩ :=
    degreeDiscrepancy_requests d t hdtotal ha herr
  let C (i : Fin m) := Finset.univ.filter (fun z => 0 < M (x i) z ∧
    0 < M z (y i) ∧ E.Adj (x i) z ∧ E.Adj z (y i))
  let B (v : V) := F.neighborFinset v
  have hxb (v : V) : ((Finset.univ.filter (fun i => x i = v)).card : ℝ) ≤ a := by
    have hh := hends v
    have hz : (0 : ℝ) ≤ (Finset.univ.filter (fun i => y i = v)).card := Nat.cast_nonneg _
    linarith
  have hyb (v : V) : ((Finset.univ.filter (fun i => y i = v)).card : ℝ) ≤ a := by
    have hh := hends v
    have hz : (0 : ℝ) ≤ (Finset.univ.filter (fun i => x i = v)).card := Nat.cast_nonneg _
    linarith
  have hB (v : V) : ((B v).card : ℝ) ≤ f := hforbid v
  have hC (i : Fin m) :
      (Fintype.card (Fin m) : ℝ) / L + 2 * a + 2 * L + 2 * f < (C i).card := by
    have hh := hpaths (x i) (y i) (hxy i i)
    have hd := div_le_div_of_nonneg_right hm (Nat.cast_nonneg L)
    simp only [Fintype.card_fin] at *
    change β * Fintype.card V ≤ (C i).card at hh
    have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  obtain ⟨z, hz, hdisj, hmiddle⟩ := twoPathPacking_exists x y C B L hL hxb hyb hB hC
  have hpath (i : Fin m) : 0 < M (x i) (z i) ∧ 0 < M (z i) (y i) :=
    ⟨(Finset.mem_filter.mp (hz i).1).2.1, (Finset.mem_filter.mp (hz i).1).2.2.1⟩
  have hloop (v : V) : M v v = 0 := by
    have hh := hphysical v v
    simp only [SimpleGraph.irrefl, ite_false] at hh
    omega
  have hxz (i : Fin m) : x i ≠ z i := by
    intro h
    have hh := (hpath i).1
    rw [h, hloop] at hh
    omega
  have hzy (i : Fin m) : z i ≠ y i := by
    intro h
    have hh := (hpath i).2
    rw [h, hloop] at hh
    omega
  let T := twoPathMultiplicity x y z
  have hT : ∀ u v, T u v ≤ M u v := twoPathMultiplicity_supported x y z M hdisj hpath
  obtain ⟨hTout, hTin⟩ := twoPathMultiplicity_degrees x y z hxz hzy
  let N := reversedMultiplicity M T
  have hNs (u v : V) : N u v + N v u = if G.Adj u v then 1 else 0 := by
    rw [reversedMultiplicity_underlying M T hT, hphysical]
  have hallowed (u v : V) (ht : 0 < T u v) : E.Adj u v ∧ ¬ F.Adj u v := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp ht
    have hp := (Finset.mem_filter.mp hi).2
    simp only [twoPathArcs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hp
    have he := (Finset.mem_filter.mp (hz i).1).2.2.2
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨he.1, by simpa [B] using (hz i).2.1⟩
    · refine ⟨he.2, ?_⟩
      have hh : ¬ F.Adj (y i) (z i) := by simpa [B] using (hz i).2.2
      exact fun h => hh h.symm
  refine ⟨N, hNs, ?_, ?_, ?_⟩
  · intro v
    have hh := reversedMultiplicity_outdegree M T hT v
    change (∑ w, N v w) + (∑ w, twoPathMultiplicity x y z v w) =
      d v + (∑ w, twoPathMultiplicity x y z w v) at hh
    rw [hTout, hTin, hx, hy] at hh
    omega
  · intro u v hchange
    by_cases ht : 0 < T u v
    · exact hallowed u v ht
    · by_cases ht' : 0 < T v u
      · obtain ⟨he, hf⟩ := hallowed v u ht'
        exact ⟨he.symm, fun h => hf h.symm⟩
      · have hzero : T u v = 0 ∧ T v u = 0 := by omega
        simp [N, reversedMultiplicity, hzero.1, hzero.2] at hchange
  · intro v
    have hh := reversedMultiplicity_changed_degree M T v
    change (Finset.univ.filter (fun w => N v w ≠ M v w ∨ N w v ≠ M w v)).card ≤
      (∑ w, twoPathMultiplicity x y z v w) +
      (∑ w, twoPathMultiplicity x y z w v) at hh
    rw [hTout, hTin] at hh
    have hr : ((Finset.univ.filter (fun w => N v w ≠ M v w ∨ N w v ≠ M w v)).card : ℝ) ≤
        ((Finset.univ.filter (fun i => x i = v)).card : ℝ) +
        middleCount Finset.univ z v +
        ((Finset.univ.filter (fun i => y i = v)).card : ℝ) +
        middleCount Finset.univ z v := by
      exact_mod_cast (by simpa only [Nat.add_assoc] using hh)
    have hm : (middleCount Finset.univ z v : ℝ) ≤ L := by exact_mod_cast hmiddle v
    linarith [hends v]

end Oberwolfach
