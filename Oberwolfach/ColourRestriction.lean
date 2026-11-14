module

public import Oberwolfach.ColourDegrees
public import Oberwolfach.DirectedCutBounds

@[expose] public section

/-! Restricting an orientation to fixed physical edge colours. Reversing
an edge changes its direction but never its colour or physical identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def colourRestriction {V : Type*} {k : ℕ} (c : Sym2 V → Fin k)
    (M : V → V → ℕ) (a : Fin k) (x y : V) : ℕ :=
  if c s(x,y) = a then M x y else 0

def edgeColourGraph {V : Type*} {k : ℕ} (G : SimpleGraph V)
    (c : Sym2 V → Fin k) (a : Fin k) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ c s(x,y) = a
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩
  loopless := by constructor; intro x h; exact (G.ne_of_adj h.1) rfl

theorem colourRestriction_sum {V : Type*} {k : ℕ} (c : Sym2 V → Fin k)
    (M : V → V → ℕ) (x y : V) :
    ∑ a, colourRestriction c M a x y = M x y := by
  simp [colourRestriction]

theorem colourRestriction_le {V : Type*} {k : ℕ} (c : Sym2 V → Fin k)
    (M : V → V → ℕ) (a : Fin k) (x y : V) :
    colourRestriction c M a x y ≤ M x y := by
  unfold colourRestriction
  split_ifs <;> omega

theorem colourRestriction_underlying {V : Type*} {k : ℕ} (G : SimpleGraph V)
    (c : Sym2 V → Fin k) (M : V → V → ℕ)
    (hphysical : ∀ x y, M x y + M y x = if G.Adj x y then 1 else 0)
    (a : Fin k) (x y : V) :
    0 < colourRestriction c M a x y + colourRestriction c M a y x ↔
      (edgeColourGraph G c a).Adj x y := by
  dsimp only [colourRestriction, edgeColourGraph]
  rw [show s(y,x) = s(x,y) from Sym2.eq_swap]
  by_cases hc : c s(x,y) = a
  · simp only [hc, ite_true, and_true, hphysical]
    split_ifs <;> simp_all
  · simp [hc]

theorem sampledColourOrientation_eq_restriction
    {V : Type*} [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (σ : Sym2 V → Fin k × Bool) (a : Fin k) (x y : V) :
    sampledColourOrientation G σ a x y =
      colourRestriction (fun e => (σ e).1) (sampledOrientation G (fun e => (σ e).2)) a x y := by
  unfold sampledColourOrientation colourRestriction sampledOrientation
  by_cases hg : G.Adj x y <;>
    by_cases hc : (σ s(x,y)).1 = a <;>
    by_cases hd : (σ s(x,y)).2 = orientationBit x y <;>
      simp [hg, hc, hd, Prod.ext_iff]

theorem boundedNat_sum_stability {V : Type*} [Fintype V]
    (f g : V → ℕ) (hf : ∀ x, f x ≤ 1) (hg : ∀ x, g x ≤ 1)
    (D : Finset V) (hsame : ∀ x, x ∉ D → f x = g x) :
    |((∑ x, f x : ℕ) : ℝ) - ((∑ x, g x : ℕ) : ℝ)| ≤ D.card := by
  have hp (x : V) : |(f x : ℝ) - g x| ≤ if x ∈ D then 1 else 0 := by
    by_cases h : x ∈ D
    · rw [ite_eq_left h]
      have hfr : (f x : ℝ) ≤ 1 := by exact_mod_cast hf x
      have hgr : (g x : ℝ) ≤ 1 := by exact_mod_cast hg x
      exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) (f x)], by linarith [Nat.cast_nonneg (α := ℝ) (g x)]⟩
    · simp [h, hsame x h]
  rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hp x)
  simpa using hs

theorem colourRestriction_degree_stability
    {V : Type*} [Fintype V] {k : ℕ} (c : Sym2 V → Fin k)
    (M N : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1) (hN : ∀ x y, N x y ≤ 1)
    (a : Fin k) (x : V) :
    |((∑ y, colourRestriction c M a x y : ℕ) : ℝ) -
      ((∑ y, colourRestriction c N a x y : ℕ) : ℝ)| ≤
      (Finset.univ.filter (fun y => M x y ≠ N x y ∨ M y x ≠ N y x)).card := by
  apply boundedNat_sum_stability
  · intro y; exact (colourRestriction_le c M a x y).trans (hM x y)
  · intro y; exact (colourRestriction_le c N a x y).trans (hN x y)
  · intro y hy
    have hh : M x y = N x y ∧ M y x = N y x := by simpa using hy
    have he := hh.1
    simp only [colourRestriction, he]

theorem colourRestriction_indegree_stability
    {V : Type*} [Fintype V] {k : ℕ} (c : Sym2 V → Fin k)
    (M N : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1) (hN : ∀ x y, N x y ≤ 1)
    (a : Fin k) (x : V) :
    |((∑ y, colourRestriction c M a y x : ℕ) : ℝ) -
      ((∑ y, colourRestriction c N a y x : ℕ) : ℝ)| ≤
      (Finset.univ.filter (fun y => M x y ≠ N x y ∨ M y x ≠ N y x)).card := by
  apply boundedNat_sum_stability
  · intro y; exact (colourRestriction_le c M a y x).trans (hM y x)
  · intro y; exact (colourRestriction_le c N a y x).trans (hN y x)
  · intro y hy
    have hh : M x y = N x y ∧ M y x = N y x := by simpa using hy
    have he := hh.2
    simp only [colourRestriction, he]

end Oberwolfach
