module

public import Oberwolfach.DisjointPatternSampling
public import Oberwolfach.OrientationRouting

@[expose] public section

/-!
Independent fair orientations of physical edges. A coordinate is an
unordered pair of vertices, so opposite arcs share one random bit.
Unused pairs have no effect on the orientation. The common event below is
chosen before a forbidden graph or a prescribed outdegree vector is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- The true bit directs the edge from its smaller to its larger endpoint. -/
def orientationBit {V : Type*} [LinearOrder V] (x y : V) : Bool := decide (x < y)

def sampledOrientation {V : Type*} [LinearOrder V] (G : SimpleGraph V)
    (σ : Sym2 V → Bool) (x y : V) : ℕ :=
  if G.Adj x y ∧ σ s(x, y) = orientationBit x y then 1 else 0

theorem sampledOrientation_physical
    {V : Type*} [LinearOrder V] (G : SimpleGraph V) (σ : Sym2 V → Bool) (x y : V) :
    sampledOrientation G σ x y + sampledOrientation G σ y x =
      if G.Adj x y then 1 else 0 := by
  by_cases hxy : G.Adj x y
  · have hyx := hxy.symm
    rcases lt_or_gt_of_ne hxy.ne with hlt | hgt
    · have hrev : ¬ y < x := not_lt_of_gt hlt
      have hs : s(y, x) = s(x, y) := Sym2.eq_swap
      cases hb : σ s(x, y) <;> simp [sampledOrientation, hxy, hyx, hs,
        orientationBit, hlt, hrev, hb]
    · have hrev : ¬ x < y := not_lt_of_gt hgt
      have hs : s(y, x) = s(x, y) := Sym2.eq_swap
      cases hb : σ s(x, y) <;> simp [sampledOrientation, hxy, hyx, hs,
        orientationBit, hgt, hrev, hb]
  · have hyx : ¬ G.Adj y x := fun h => hxy h.symm
    simp [sampledOrientation, hxy, hyx]

def twoEdgeCoordinates {V : Type*} [DecidableEq V] (x y z : V) : Finset (Sym2 V) :=
  {s(x, z), s(z, y)}

def twoEdgeRequirements {V : Type*} [LinearOrder V] (x y z : V) (e : Sym2 V) : Bool :=
  if e = s(x, z) then orientationBit x z else orientationBit z y

theorem twoEdgeCoordinates_card
    {V : Type*} [DecidableEq V] {x y z : V} (hxy : x ≠ y) :
    (twoEdgeCoordinates x y z).card = 2 := by
  have he : s(x, z) ≠ s(z, y) := by
    simp only [ne_eq, Sym2.eq_iff]
    aesop
  simp [twoEdgeCoordinates, he]

theorem twoEdgeCoordinates_disjoint
    {V : Type*} [DecidableEq V] {x y z w : V}
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (_hwx : w ≠ x) (_hwy : w ≠ y) (hzw : z ≠ w) :
    Disjoint (twoEdgeCoordinates x y z) (twoEdgeCoordinates x y w) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  simp only [twoEdgeCoordinates, Finset.mem_insert, Finset.mem_singleton] at he hf
  rcases he with rfl | rfl <;> rcases hf with hf | hf <;>
    simp only [Sym2.eq_iff] at hf <;> tauto

theorem sampledOrientation_degree_patterns
    {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (σ : Sym2 V → Bool) (x : V) :
    ((∑ y, sampledOrientation G σ x y : ℕ) : ℝ) =
      ∑ y ∈ G.neighborFinset x,
        patternValue {s(x, y)} (fun _ => orientationBit x y) σ := by
  have hn : G.neighborFinset x = Finset.univ.filter (G.Adj x) := by
    ext y
    simp
  rw [hn, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  by_cases ha : G.Adj x y <;> simp [sampledOrientation, ha, patternValue]

theorem sampledOrientation_degree_tail
    {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin)).probability (fun σ =>
      t ≤ |((∑ y, sampledOrientation G σ x y : ℕ) : ℝ) - (G.degree x : ℝ) / 2|) ≤
      2 * Real.exp (-2 * t ^ 2 / G.degree x) := by
  have hdisj : ∀ y ∈ G.neighborFinset x, ∀ z ∈ G.neighborFinset x, y ≠ z →
      Disjoint ({s(x, y)} : Finset (Sym2 V)) {s(x, z)} := by
    intro y _ z _ hyz
    simp only [Finset.disjoint_singleton_left, Finset.mem_singleton, Sym2.eq_iff]
    aesop
  have hh := finiteLaw_fair_disjoint_patterns_tail (G.neighborFinset x)
    (fun y => ({s(x, y)} : Finset (Sym2 V))) (fun y _ => orientationBit x y) 1
    (fun _ _ => Finset.card_singleton _) hdisj ht
  simp only [← sampledOrientation_degree_patterns, SimpleGraph.card_neighborFinset_eq_degree,
    pow_one, Nat.cast_one, mul_one] at hh
  simpa only [div_eq_mul_inv, one_div, one_mul] using hh

theorem sampledOrientation_twoPath_pattern
    {V : Type*} [LinearOrder V] (G : SimpleGraph V) (σ : Sym2 V → Bool)
    {x y z : V} (hxy : x ≠ y) (hxz : G.Adj x z) (hzy : G.Adj z y) :
    patternValue (twoEdgeCoordinates x y z) (twoEdgeRequirements x y z) σ =
      if 0 < sampledOrientation G σ x z ∧ 0 < sampledOrientation G σ z y then 1 else 0 := by
  have he : s(z, y) ≠ s(x, z) := by
    simp only [ne_eq, Sym2.eq_iff]
    aesop
  simp only [patternValue_indicator, twoEdgeCoordinates, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  simp only [twoEdgeRequirements, ite_eq_right he]
  by_cases h1 : σ s(x, z) = orientationBit x z <;>
    by_cases h2 : σ s(z, y) = orientationBit z y <;>
      simp [sampledOrientation, hxz, hzy, h1, h2]

/-- Common neighbours whose two incident edges have the directions x to z
and z to y. The eligibility graph E is fixed before the orientation. -/
def eligibleTwoPathCount {V : Type*} [Fintype V] (E : SimpleGraph V)
    (M : V → V → ℕ) (x y : V) : ℕ :=
  ((E.neighborFinset x ∩ E.neighborFinset y).filter
    (fun z => 0 < M x z ∧ 0 < M z y)).card

theorem sampledOrientation_twoPath_patterns
    {V : Type*} [Fintype V] [LinearOrder V] (G E : SimpleGraph V) (hEG : E ≤ G)
    (σ : Sym2 V → Bool) {x y : V} (hxy : x ≠ y) :
    (eligibleTwoPathCount E (sampledOrientation G σ) x y : ℝ) =
      ∑ z ∈ E.neighborFinset x ∩ E.neighborFinset y,
        patternValue (twoEdgeCoordinates x y z) (twoEdgeRequirements x y z) σ := by
  rw [eligibleTwoPathCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hxz : E.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
  have hyz : E.Adj y z := by simpa using (Finset.mem_inter.mp hz).2
  rw [sampledOrientation_twoPath_pattern G σ hxy (hEG hxz) (hEG hyz.symm)]
  split_ifs <;> norm_num

theorem sampledOrientation_twoPath_tail
    {V : Type*} [Fintype V] [LinearOrder V] (G E : SimpleGraph V) (hEG : E ≤ G)
    {x y : V} (hxy : x ≠ y) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin)).probability (fun σ =>
      t ≤ |(eligibleTwoPathCount E (sampledOrientation G σ) x y : ℝ) -
        ((E.neighborFinset x ∩ E.neighborFinset y).card : ℝ) / 4|) ≤
      2 * Real.exp (-2 * t ^ 2 /
        (((E.neighborFinset x ∩ E.neighborFinset y).card : ℝ) * 2)) := by
  let C := E.neighborFinset x ∩ E.neighborFinset y
  have hne (z : V) (hz : z ∈ C) : z ≠ x ∧ z ≠ y := by
    have hxz : E.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
    have hyz : E.Adj y z := by simpa using (Finset.mem_inter.mp hz).2
    exact ⟨hxz.ne.symm, hyz.ne.symm⟩
  have hdisj : ∀ z ∈ C, ∀ w ∈ C, z ≠ w →
      Disjoint (twoEdgeCoordinates x y z) (twoEdgeCoordinates x y w) := by
    intro z hz w hw hzw
    exact twoEdgeCoordinates_disjoint hxy (hne z hz).1 (hne z hz).2
      (hne w hw).1 (hne w hw).2 hzw
  have hh := finiteLaw_fair_disjoint_patterns_tail C (twoEdgeCoordinates x y)
    (twoEdgeRequirements x y) 2 (fun _ _ => twoEdgeCoordinates_card hxy) hdisj ht
  have hcenter : (C.card : ℝ) * (1 / 2 : ℝ) ^ 2 = (C.card : ℝ) / 4 := by ring
  rw [hcenter] at hh
  simpa only [C, ← sampledOrientation_twoPath_patterns G E hEG _ hxy, Nat.cast_ofNat] using hh

theorem sampledOrientation_twoPath_lower_tail
    {V : Type*} [Fintype V] [LinearOrder V] (G E : SimpleGraph V) (hEG : E ≤ G)
    {x y : V} (hxy : x ≠ y) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin)).probability (fun σ =>
      (eligibleTwoPathCount E (sampledOrientation G σ) x y : ℝ) ≤
        ((E.neighborFinset x ∩ E.neighborFinset y).card : ℝ) / 8) ≤
      2 * Real.exp (-((E.neighborFinset x ∩ E.neighborFinset y).card : ℝ) / 64) := by
  let m : ℝ := (E.neighborFinset x ∩ E.neighborFinset y).card
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hh := sampledOrientation_twoPath_tail G E hEG hxy (t := m / 8) (by positivity)
  have hmono := finiteLaw_probability_mono
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin))
    (fun σ => (eligibleTwoPathCount E (sampledOrientation G σ) x y : ℝ) ≤ m / 8)
    (fun σ => m / 8 ≤ |(eligibleTwoPathCount E (sampledOrientation G σ) x y : ℝ) - m / 4|)
    (fun σ h => by
      have ha := neg_le_abs ((eligibleTwoPathCount E (sampledOrientation G σ) x y : ℝ) - m / 4)
      linarith)
  have heq : -2 * (m / 8) ^ 2 / (m * 2) = -m / 64 := by
    by_cases hz : m = 0
    · simp [hz]
    · field_simp
      ring
  change _ ≤ 2 * Real.exp (-2 * (m / 8) ^ 2 / (m * 2)) at hh
  rw [heq] at hh
  exact hmono.trans hh

/-- A single event controls all vertices and all distinct ordered pairs.
The failure sum is explicit; no later forbidden graph enters the event. -/
theorem sampledOrientation_common_event
    {V : Type*} [Fintype V] [LinearOrder V] (G E : SimpleGraph V) (hEG : E ≤ G)
    {t : ℝ} (ht : 0 ≤ t) :
    1 - ((∑ x : V, 2 * Real.exp (-2 * t ^ 2 / G.degree x)) +
      (∑ p : {p : V × V // p.1 ≠ p.2},
        2 * Real.exp (-((E.neighborFinset p.1.1 ∩ E.neighborFinset p.1.2).card : ℝ) / 64))) ≤
      (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin)).probability (fun σ =>
        (∀ x, |((∑ y, sampledOrientation G σ x y : ℕ) : ℝ) - (G.degree x : ℝ) / 2| < t) ∧
        ∀ x y, x ≠ y → ((E.neighborFinset x ∩ E.neighborFinset y).card : ℝ) / 8 <
          (eligibleTwoPathCount E (sampledOrientation G σ) x y : ℝ)) := by
  let J := V ⊕ {p : V × V // p.1 ≠ p.2}
  let A : J → (Sym2 V → Bool) → Prop := Sum.elim
    (fun x σ => t ≤ |((∑ y, sampledOrientation G σ x y : ℕ) : ℝ) - (G.degree x : ℝ) / 2|)
    (fun p σ => (eligibleTwoPathCount E (sampledOrientation G σ) p.1.1 p.1.2 : ℝ) ≤
      ((E.neighborFinset p.1.1 ∩ E.neighborFinset p.1.2).card : ℝ) / 8)
  let b : J → ℝ := Sum.elim
    (fun x => 2 * Real.exp (-2 * t ^ 2 / G.degree x))
    (fun p => 2 * Real.exp (-((E.neighborFinset p.1.1 ∩ E.neighborFinset p.1.2).card : ℝ) / 64))
  have hb : ∀ j ∈ (Finset.univ : Finset J),
      (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin)).probability (A j) ≤ b j := by
    intro j _
    cases j with
    | inl x => exact sampledOrientation_degree_tail G x ht
    | inr p => exact sampledOrientation_twoPath_lower_tail G E hEG p.2
  have hh := finiteLaw_common_event_lower
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin)) Finset.univ A b hb
  simpa only [J, Fintype.sum_sum_type, b, A, Sum.elim_inl, Sum.elim_inr,
    Finset.mem_univ, forall_const, Sum.forall, not_le, Subtype.forall, Prod.forall] using hh

theorem commonNeighbours_of_minDegree
    {V : Type*} [Fintype V] (G : SimpleGraph V) {α : ℝ}
    (hdeg : ∀ v, (1 / 2 + α) * Fintype.card V ≤ (G.degree v : ℝ)) (x y : V) :
    2 * α * Fintype.card V ≤ ((G.neighborFinset x ∩ G.neighborFinset y).card : ℝ) := by
  have hc := Finset.card_inter_add_card_union (G.neighborFinset x) (G.neighborFinset y)
  have hu : (G.neighborFinset x ∪ G.neighborFinset y).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  have hr : ((G.neighborFinset x ∩ G.neighborFinset y).card : ℝ) +
      ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) =
      (G.degree x : ℝ) + G.degree y := by
    exact_mod_cast (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hc)
  have hur : ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hu
  linarith [hdeg x, hdeg y]

theorem halfDegrees_total
    {V : Type*} [Fintype V] (G : SimpleGraph V) (d : V → ℕ)
    (hd : ∀ v, 2 * d v = G.degree v) : ∑ v, d v = G.edgeFinset.card := by
  have hh := G.sum_degrees_eq_twice_card_edges
  simp only [← hd, ← Finset.mul_sum] at hh
  omega

theorem eligibleTwoPathCount_as_filter
    {V : Type*} [Fintype V] (E : SimpleGraph V) (M : V → V → ℕ) (x y : V) :
    eligibleTwoPathCount E M x y =
      (Finset.univ.filter (fun z => 0 < M x z ∧ 0 < M z y ∧ E.Adj x z ∧ E.Adj z y)).card := by
  unfold eligibleTwoPathCount
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨hxz, hyz⟩, hp, hq⟩
    exact ⟨hp, hq, hxz, hyz.symm⟩
  · rintro ⟨hp, hq, hxz, hzy⟩
    exact ⟨⟨hxz, hzy.symm⟩, hp, hq⟩

/-- The routing conclusion holds for every later forbidden graph on one
orientation event. The degree vector is exactly half the undirected degree;
its total and the physical/auxiliary conversion are proved here. -/
theorem sampledOrientation_balancing_event
    {V : Type*} [Fintype V] [LinearOrder V] (G E : SimpleGraph V) (hEG : E ≤ G)
    (d : V → ℕ) (hd : ∀ v, 2 * d v = G.degree v)
    (L : ℕ) (hL : 0 < L) (hn : 0 < Fintype.card V)
    {a f β : ℝ} (ha : 0 ≤ a) (hf : 0 ≤ f) (hβ : 0 < β)
    (hcommon : ∀ x y, x ≠ y → 8 * β * Fintype.card V ≤
      ((E.neighborFinset x ∩ E.neighborFinset y).card : ℝ))
    (hmargin : (Fintype.card V : ℝ) * a / L + 2 * a + 4 * L + 2 * f < β * Fintype.card V) :
    1 - ((∑ x : V, 2 * Real.exp (-2 * a ^ 2 / G.degree x)) +
      (∑ p : {p : V × V // p.1 ≠ p.2},
        2 * Real.exp (-((E.neighborFinset p.1.1 ∩ E.neighborFinset p.1.2).card : ℝ) / 64))) ≤
      (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin)).probability (fun σ =>
        ∀ F : SimpleGraph V, (∀ v, (F.degree v : ℝ) ≤ f) →
        ∃ N : V → V → ℕ,
          (∀ x y, N x y + N y x = if G.Adj x y then 1 else 0) ∧
          (∀ v, ∑ w, N v w = d v) ∧
          (∀ x y, N x y ≠ sampledOrientation G σ x y ∨
            N y x ≠ sampledOrientation G σ y x → E.Adj x y ∧ ¬ F.Adj x y) ∧
          ∀ x, ((Finset.univ.filter (fun y => N x y ≠ sampledOrientation G σ x y ∨
            N y x ≠ sampledOrientation G σ y x)).card : ℝ) ≤ a + 2 * L) := by
  apply (sampledOrientation_common_event G E hEG ha).trans
  apply finiteLaw_probability_mono
  intro σ hσ F hF
  apply orientationRouting G E F (sampledOrientation G σ) d L hL hn ha hf hβ
    (sampledOrientation_physical G σ) (halfDegrees_total G d hd)
  · intro v
    have hdreal : (d v : ℝ) = (G.degree v : ℝ) / 2 := by
      have h := hd v
      have hr : (2 : ℝ) * d v = G.degree v := by exact_mod_cast h
      linarith
    rw [hdreal]
    exact (hσ.1 v).le
  · exact hF
  · intro x y hxy
    have hh := hσ.2 x y hxy
    have hc := hcommon x y hxy
    rw [eligibleTwoPathCount_as_filter] at hh
    linarith
  · exact hmargin

end Oberwolfach
