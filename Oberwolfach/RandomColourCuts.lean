module

public import Oberwolfach.GraphCuts
public import Oberwolfach.RandomOrientation

@[expose] public section

/-! Raw directed-colour cuts, indexed by physical unordered edges. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def sampledColourOrientation {V : Type*} [LinearOrder V] {k : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin k × Bool) (a : Fin k) (x y : V) : ℕ :=
  if G.Adj x y ∧ σ s(x, y) = (a, orientationBit x y) then 1 else 0

theorem sampledColourOrientation_sum
    {V : Type*} [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (σ : Sym2 V → Fin k × Bool) (x y : V) :
    (∑ a, sampledColourOrientation G σ a x y) =
      sampledOrientation G (fun e => (σ e).2) x y := by
  have hp (a : Fin k) : sampledColourOrientation G σ a x y =
      if a = (σ s(x, y)).1 then sampledOrientation G (fun e => (σ e).2) x y else 0 := by
    unfold sampledColourOrientation sampledOrientation
    by_cases hg : G.Adj x y <;>
      by_cases ha : a = (σ s(x, y)).1 <;>
      by_cases hb : (σ s(x, y)).2 = orientationBit x y <;>
        simp [hg, ha, hb, Prod.ext_iff, eq_comm]
  simp only [hp]
  simp

theorem sampledColourOrientation_physical
    {V : Type*} [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (σ : Sym2 V → Fin k × Bool) (x y : V) :
    (∑ a, (sampledColourOrientation G σ a x y + sampledColourOrientation G σ a y x)) =
      if G.Adj x y then 1 else 0 := by
  rw [Finset.sum_add_distrib, sampledColourOrientation_sum, sampledColourOrientation_sum]
  exact sampledOrientation_physical G (fun e => (σ e).2) x y

def orderedGraphCutEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Finset V) : Finset (V × V) :=
  (S ×ˢ T).filter (fun p => G.Adj p.1 p.2)

theorem orderedGraphCutEdges_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Finset V) :
    (orderedGraphCutEdges G S T).card = graphCut G S T := by
  rw [orderedGraphCutEdges, Finset.card_filter, Finset.sum_product, graphCut_eq_sum]

theorem unorderedPair_fiber_bound
    {V : Type*} [DecidableEq V] (C : Finset (V × V)) (e : Sym2 V) :
    (C.filter (fun p => s(p.1, p.2) = e)).card ≤ 2 := by
  classical
  have hs : C.filter (fun p => s(p.1, p.2) = e) ⊆ {e.out, e.out.swap} := by
    intro p hp
    have he := (Finset.mem_filter.mp hp).2
    have hout : s(e.out.1, e.out.2) = e := e.out_eq
    rw [← hout, Sym2.eq_iff] at he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  exact (Finset.card_le_card hs).trans
    ((Finset.card_insert_le _ _).trans (by simp))

theorem sampledColourCut_patterns
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (σ : Sym2 V → Fin k × Bool) (a : Fin k) (S T : Finset V) :
    ((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) =
      ∑ p ∈ orderedGraphCutEdges G S T,
        patternValue {s(p.1, p.2)} (fun _ => (a, orientationBit p.1 p.2)) σ := by
  rw [orderedGraphCutEdges, Finset.sum_filter, Finset.sum_product]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases ha : G.Adj x y <;> simp [sampledColourOrientation, patternValue, ha]

/-- A direct bound for the actual directed-colour cut. A physical edge can
occur in the ordered cut at most twice. This gives a conservative influence
bound of two, sufficient for the exponentially small large-cut failure. -/
theorem sampledColourCut_tail
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (S T : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => t ≤ |((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
        ρ a / 2 * graphCut G S T|) ≤
      2 * Real.exp (-2 * t ^ 2 / (4 * Fintype.card (Sym2 V))) := by
  let C := orderedGraphCutEdges G S T
  have hload (e : Sym2 V) :
      (∑ p ∈ C, if e ∈ ({s(p.1, p.2)} : Finset (Sym2 V)) \ ∅ then (1 : ℝ) else 0) ≤ 2 := by
    have hh := unorderedPair_fiber_bound C e
    have hr : ((C.filter (fun p => s(p.1, p.2) = e)).card : ℝ) ≤ 2 := by exact_mod_cast hh
    simpa only [Finset.sdiff_empty, Finset.mem_singleton, eq_comm, Finset.card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hr
  have hh := finiteLaw_omitted_weighted_tail
    (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)
    C (fun p => {s(p.1, p.2)}) ∅ (fun p _ => (a, orientationBit p.1 p.2))
    (fun _ => 1) (fun _ => 2) (fun _ _ => zero_le_one) hload ht
  have hmass (s : Fin k × Bool) :
      (FiniteLaw.categoricalDirection ρ hρ htotal).mass s = ρ s.1 / 2 := rfl
  simp only [Finset.sdiff_empty, one_mul, Finset.prod_singleton,
    hmass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  have hm : (C.card : ℝ) * (ρ a / 2) = ρ a / 2 * graphCut G S T := by
    dsimp only [C]
    rw [orderedGraphCutEdges_card]
    ring
  rw [hm] at hh
  simpa only [C, ← sampledColourCut_patterns G _ a S T, mul_comm (Fintype.card (Sym2 V) : ℝ),
    show (2 : ℝ) ^ 2 = 4 by norm_num] using hh

theorem card_unorderedPairs_le_square
    {V : Type*} [Fintype V] : Fintype.card (Sym2 V) ≤ (Fintype.card V) ^ 2 := by
  have hs : Function.Surjective (fun p : V × V => s(p.1, p.2)) :=
    fun e => ⟨e.out, e.out_eq⟩
  simpa only [Fintype.card_prod, pow_two] using Fintype.card_le_of_surjective _ hs

theorem sampledColourCut_uniform_tail
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (hn : 0 < Fintype.card V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (S T : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => t ≤ |((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
        ρ a / 2 * graphCut G S T|) ≤
      2 * Real.exp (-t ^ 2 / (2 * (Fintype.card V : ℝ) ^ 2)) := by
  have : Nonempty V := Fintype.card_pos_iff.mp hn
  let v : V := Classical.choice this
  have : Nonempty (Sym2 V) := ⟨s(v, v)⟩
  have hm : (0 : ℝ) < Fintype.card (Sym2 V) := by exact_mod_cast Fintype.card_pos (α := Sym2 V)
  have hc : (Fintype.card (Sym2 V) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast (card_unorderedPairs_le_square (V := V))
  apply (sampledColourCut_tail G ρ hρ htotal a S T ht).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_left (show 0 ≤ (2 : ℝ) * t ^ 2 by positivity)
    (show 0 < 4 * (Fintype.card (Sym2 V) : ℝ) by positivity)
    (show 4 * (Fintype.card (Sym2 V) : ℝ) ≤ 4 * (Fintype.card V : ℝ) ^ 2 by linarith)
  have heq : -t ^ 2 / (2 * (Fintype.card V : ℝ) ^ 2) =
      -(2 * t ^ 2 / (4 * (Fintype.card V : ℝ) ^ 2)) := by ring
  rw [heq]
  simpa only [neg_mul, neg_div] using neg_le_neg hh

/-- All colours and all cuts are controlled on one joint sample. Both
ordered occurrences of an edge in overlapping cuts use its single state. -/
theorem sampledColourCut_all_cuts
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (hn : 0 < Fintype.card V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (t : Fin k → ℝ) (ht : ∀ a, 0 ≤ t a) :
    1 - (4 : ℝ) ^ Fintype.card V *
      (∑ a, 2 * Real.exp (-(t a) ^ 2 / (2 * (Fintype.card V : ℝ) ^ 2))) ≤
      (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
        (fun σ => ∀ a S T,
          |((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
            ρ a / 2 * graphCut G S T| < t a) := by
  let J := Fin k × (Finset V × Finset V)
  let A (j : J) (σ : Sym2 V → Fin k × Bool) :=
    t j.1 ≤ |((∑ x ∈ j.2.1, ∑ y ∈ j.2.2, sampledColourOrientation G σ j.1 x y : ℕ) : ℝ) -
      ρ j.1 / 2 * graphCut G j.2.1 j.2.2|
  let b (j : J) := 2 * Real.exp (-(t j.1) ^ 2 / (2 * (Fintype.card V : ℝ) ^ 2))
  have hh := finiteLaw_common_event_lower
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal))
    Finset.univ A b (fun j _ => sampledColourCut_uniform_tail G hn ρ hρ htotal
      j.1 j.2.1 j.2.2 (ht j.1))
  have hc : (Fintype.card (Finset V × Finset V) : ℝ) = (4 : ℝ) ^ Fintype.card V := by
    simp only [Fintype.card_prod, Fintype.card_finset, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]
    norm_num
  have hsum : (∑ j : J, b j) = (4 : ℝ) ^ Fintype.card V *
      (∑ a, 2 * Real.exp (-(t a) ^ 2 / (2 * (Fintype.card V : ℝ) ^ 2))) := by
    rw [Fintype.sum_prod_type]
    simp only [b, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    rw [Finset.mul_sum]
  rw [hsum] at hh
  simpa only [A, J, Finset.mem_univ, forall_const, Prod.forall, not_le] using hh

end Oberwolfach
