module

public import Oberwolfach.FiniteLawMap
public import Oberwolfach.DisjointSingletonSampling
public import Oberwolfach.RandomColourCuts

@[expose] public section

/-! Vertex degree and protected-subgraph degree tests for the raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem incidentPair_injective
    {V : Type*} (x : V) : Function.Injective (fun y => s(x, y)) := by
  intro y z h
  rcases Sym2.eq_iff.mp h with ⟨_, he⟩ | ⟨h1, h2⟩
  · exact he
  · exact h2.trans h1

theorem sampledColourOrientation_degree_patterns
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (σ : Sym2 V → Fin k × Bool) (a : Fin k) (x : V) :
    ((∑ y, sampledColourOrientation G σ a x y : ℕ) : ℝ) =
      ∑ y ∈ G.neighborFinset x,
        patternValue {s(x, y)} (fun _ => (a, orientationBit x y)) σ := by
  have hn : G.neighborFinset x = Finset.univ.filter (G.Adj x) := by ext y; simp
  rw [hn, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  by_cases ha : G.Adj x y <;> simp [sampledColourOrientation, patternValue, ha]

theorem sampledColourOrientation_degree_tail
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (x : V) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => t ≤ |((∑ y, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
        ρ a / 2 * G.degree x|) ≤
      2 * Real.exp (-2 * t ^ 2 / Fintype.card V) := by
  have hh := finiteLaw_singleton_patterns_tail_at_scale
    (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)
    (G.neighborFinset x) (fun y => s(x, y)) (fun y _ => (a, orientationBit x y))
    (fun _ _ _ _ h => incidentPair_injective x h)
    (n := Fintype.card V) (by exact_mod_cast (G.degree_lt_card_verts x).le) ht
  have hmass (b : Bool) :
      (FiniteLaw.categoricalDirection ρ hρ htotal).mass (a, b) = ρ a / 2 := rfl
  simp only [hmass, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
    ← sampledColourOrientation_degree_patterns] at hh
  have heq : (G.degree x : ℝ) * (ρ a / 2) = ρ a / 2 * G.degree x := mul_comm _ _
  simpa only [heq] using hh

theorem sampledColourOrientation_indegree_patterns
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (σ : Sym2 V → Fin k × Bool) (a : Fin k) (x : V) :
    ((∑ y, sampledColourOrientation G σ a y x : ℕ) : ℝ) =
      ∑ y ∈ G.neighborFinset x,
        patternValue {s(y, x)} (fun _ => (a, orientationBit y x)) σ := by
  have hn : G.neighborFinset x = Finset.univ.filter (G.Adj x) := by ext y; simp
  rw [hn, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  by_cases ha : G.Adj x y
  · simp [sampledColourOrientation, patternValue, ha, ha.symm]
  · have hy : ¬ G.Adj y x := fun h => ha h.symm
    simp [sampledColourOrientation, ha, hy]

theorem sampledColourOrientation_indegree_tail
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (x : V) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => t ≤ |((∑ y, sampledColourOrientation G σ a y x : ℕ) : ℝ) -
        ρ a / 2 * G.degree x|) ≤
      2 * Real.exp (-2 * t ^ 2 / Fintype.card V) := by
  have hinj : Function.Injective (fun y => s(y, x)) := by
    intro y z h
    have h' : s(x, y) = s(x, z) := Sym2.eq_swap.trans (h.trans Sym2.eq_swap)
    exact incidentPair_injective x h'
  have hh := finiteLaw_singleton_patterns_tail_at_scale
    (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)
    (G.neighborFinset x) (fun y => s(y, x)) (fun y _ => (a, orientationBit y x))
    (fun _ _ _ _ h => hinj h)
    (n := Fintype.card V) (by exact_mod_cast (G.degree_lt_card_verts x).le) ht
  have hmass (b : Bool) :
      (FiniteLaw.categoricalDirection ρ hρ htotal).mass (a, b) = ρ a / 2 := rfl
  simp only [hmass, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
    ← sampledColourOrientation_indegree_patterns] at hh
  have heq : (G.degree x : ℝ) * (ρ a / 2) = ρ a / 2 * G.degree x := mul_comm _ _
  simpa only [heq] using hh

/-- Undirected colour degree inside a fixed graph Z. The graph Z is
chosen before sampling; no direction is tested. -/
def sampledColourDegree {V : Type*} [Fintype V] {k : ℕ}
    (Z : SimpleGraph V) (c : Sym2 V → Fin k) (a : Fin k) (x : V) : ℕ :=
  ((Z.neighborFinset x).filter (fun y => c s(x, y) = a)).card

theorem sampledColourDegree_patterns
    {V : Type*} [Fintype V] {k : ℕ} (Z : SimpleGraph V)
    (c : Sym2 V → Fin k) (a : Fin k) (x : V) :
    (sampledColourDegree Z c a x : ℝ) =
      ∑ y ∈ Z.neighborFinset x, patternValue {s(x, y)} (fun _ => a) c := by
  rw [sampledColourDegree, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp [patternValue]

theorem sampledColourDegree_tail
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (Z : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (x : V) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ htotal)).probability
      (fun c => t ≤ |(sampledColourDegree Z c a x : ℝ) - ρ a * Z.degree x|) ≤
      2 * Real.exp (-2 * t ^ 2 / Fintype.card V) := by
  have hh := finiteLaw_singleton_patterns_tail_at_scale
    (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ htotal)
    (Z.neighborFinset x) (fun y => s(x, y)) (fun _ _ => a)
    (fun _ _ _ _ h => incidentPair_injective x h)
    (n := Fintype.card V) (by exact_mod_cast (Z.degree_lt_card_verts x).le) ht
  have hmass : (FiniteLaw.categorical ρ hρ htotal).mass a = ρ a := rfl
  simp only [hmass, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
    ← sampledColourDegree_patterns] at hh
  simpa only [mul_comm (Z.degree x : ℝ)] using hh

theorem sampledColourDegree_joint_tail
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (Z : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (x : V) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => t ≤ |(sampledColourDegree Z (fun e => (σ e).1) a x : ℝ) - ρ a * Z.degree x|) ≤
      2 * Real.exp (-2 * t ^ 2 / Fintype.card V) := by
  have hm := categoricalDirection_colour_probability (E := Sym2 V) ρ hρ htotal
    (fun c => t ≤ |(sampledColourDegree Z c a x : ℝ) - ρ a * Z.degree x|)
  rw [hm]
  exact sampledColourDegree_tail Z ρ hρ htotal a x ht

end Oberwolfach
