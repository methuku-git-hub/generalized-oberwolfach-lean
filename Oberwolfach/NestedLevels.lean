module

public import Oberwolfach.NestedCounts
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! The unique shell containing a vertex of a nested finite sequence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def nestedLevel {V : Type*} (B : ℕ → Finset V) (t : ℕ) (x : V) : ℕ :=
  Nat.findGreatest (fun i => x ∈ B i) t

theorem nestedLevel_le {V : Type*} (B : ℕ → Finset V) (t : ℕ) (x : V) :
    nestedLevel B t x ≤ t :=
  Nat.findGreatest_le t

theorem mem_nestedLevel {V : Type*} [Fintype V] (B : ℕ → Finset V) (t : ℕ)
    (hzero : B 0 = Finset.univ) (x : V) : x ∈ B (nestedLevel B t x) :=
  Nat.findGreatest_spec (P := fun i => x ∈ B i) (Nat.zero_le t)
    (by rw [hzero]; exact Finset.mem_univ x)

theorem mem_nested_iff_le_level {V : Type*} [Fintype V]
    (B : ℕ → Finset V) (t : ℕ) (hzero : B 0 = Finset.univ)
    (hsub : ∀ i < t, B (i + 1) ⊆ B i) (x : V) {i : ℕ} (hi : i ≤ t) :
    x ∈ B i ↔ i ≤ nestedLevel B t x := by
  constructor
  · exact fun hx => Nat.le_findGreatest hi hx
  · intro hix
    exact finset_chain_subset B t hsub hix (nestedLevel_le B t x) (mem_nestedLevel B t hzero x)

theorem nestedLevel_fibre_last {V : Type*} [Fintype V]
    (B : ℕ → Finset V) (t : ℕ) (hzero : B 0 = Finset.univ)
    (hsub : ∀ i < t, B (i + 1) ⊆ B i) :
    Finset.univ.filter (fun x => nestedLevel B t x = t) = B t := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_nested_iff_le_level B t hzero hsub x (le_refl t)]
  have := nestedLevel_le B t x
  omega

theorem nestedLevel_fibre_shell {V : Type*} [Fintype V]
    (B : ℕ → Finset V) (t : ℕ) (hzero : B 0 = Finset.univ)
    (hsub : ∀ i < t, B (i + 1) ⊆ B i) {i : ℕ} (hi : i < t) :
    Finset.univ.filter (fun x => nestedLevel B t x = i) = B i \ B (i + 1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  rw [mem_nested_iff_le_level B t hzero hsub x (by omega : i ≤ t),
    mem_nested_iff_le_level B t hzero hsub x (by omega : i + 1 ≤ t)]
  omega

end Oberwolfach
