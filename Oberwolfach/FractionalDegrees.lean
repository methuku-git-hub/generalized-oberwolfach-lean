module

public import Oberwolfach.RealFlow
public import Oberwolfach.NormalizedDemands

@[expose] public section

/-!
The real-valued part of the prescribed-degree criterion. The edge type
is retained throughout; no parallel copies are collapsed.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def bipartiteNetworkTail {X Y E : Type*} (tail : E → X) :
    X ⊕ E ⊕ Y → Bool ⊕ X ⊕ Y
  | .inl _ => .inl false
  | .inr (.inl e) => .inr (.inl (tail e))
  | .inr (.inr y) => .inr (.inr y)

def bipartiteNetworkHead {X Y E : Type*} (head : E → Y) :
    X ⊕ E ⊕ Y → Bool ⊕ X ⊕ Y
  | .inl x => .inr (.inl x)
  | .inr (.inl e) => .inr (.inr (head e))
  | .inr (.inr _) => .inl true

def bipartiteNetworkCapacity {X Y E : Type*}
    (f : X → ℝ) (g : Y → ℝ) (c : E → ℝ) : X ⊕ E ⊕ Y → ℝ
  | .inl x => f x
  | .inr (.inl e) => c e
  | .inr (.inr y) => g y

theorem bipartiteNetwork_divergence
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (q : X ⊕ E ⊕ Y → ℝ) :
    flowDivergence (bipartiteNetworkTail tail) (bipartiteNetworkHead head) q
      (.inl false) = ∑ x, q (.inl x) ∧
    flowDivergence (bipartiteNetworkTail tail) (bipartiteNetworkHead head) q
      (.inl true) = -(∑ y, q (.inr (.inr y))) ∧
    (∀ x, flowDivergence (bipartiteNetworkTail tail) (bipartiteNetworkHead head) q
      (.inr (.inl x)) = (∑ e, if tail e = x then q (.inr (.inl e)) else 0) -
        q (.inl x)) ∧
    (∀ y, flowDivergence (bipartiteNetworkTail tail) (bipartiteNetworkHead head) q
      (.inr (.inr y)) = q (.inr (.inr y)) -
        ∑ e, if head e = y then q (.inr (.inl e)) else 0) := by
  simp [flowDivergence, vertexDifference, Fintype.sum_sum_type,
    bipartiteNetworkTail, bipartiteNetworkHead, mul_ite, Finset.sum_neg_distrib,
    sub_eq_add_neg, add_comm]

set_option backward.isDefEq.respectTransparency false in
theorem bipartiteNetwork_cut
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (f : X → ℝ) (g : Y → ℝ) (c : E → ℝ)
    (R : Finset (Bool ⊕ X ⊕ Y)) (hs : Sum.inl false ∈ R) (ht : Sum.inl true ∉ R) :
    networkCutCapacity (bipartiteNetworkTail tail) (bipartiteNetworkHead head)
      (bipartiteNetworkCapacity f g c) R =
      (∑ x, if Sum.inr (Sum.inl x) ∉ R then f x else 0) +
      (∑ e, if Sum.inr (Sum.inl (tail e)) ∈ R ∧
        Sum.inr (Sum.inr (head e)) ∉ R then c e else 0) +
      ∑ y, if Sum.inr (Sum.inr y) ∈ R then g y else 0 := by
  simp [networkCutCapacity, Fintype.sum_sum_type, bipartiteNetworkTail,
    bipartiteNetworkHead, bipartiteNetworkCapacity, hs, ht, add_assoc]

/-- Real demands are feasible exactly under the bipartite cut inequalities.
This direction supplies the fractional edge weights used later in the
manuscript; the integer version is proved separately by Hall's theorem. -/
theorem bipartite_fractionalDegrees
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (c : E → ℝ)
    (f : X → ℝ) (g : Y → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y)
    (htotal : ∑ x, f x = ∑ y, g y)
    (hcut : ∀ S : Finset X, ∀ T : Finset Y,
      ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
        ∑ e, if tail e ∈ S ∧ head e ∉ T then c e else 0) :
    ∃ q : E → ℝ, CapacityBounded c q ∧
      (∀ x, (∑ e, if tail e = x then q e else 0) = f x) ∧
      (∀ y, (∑ e, if head e = y then q e else 0) = g y) := by
  classical
  let a := bipartiteNetworkTail (Y := Y) tail
  let b := bipartiteNetworkHead (X := X) head
  let cap := bipartiteNetworkCapacity f g c
  have hcap : ∀ e, 0 ≤ cap e := by
    rintro (x | e | y)
    · exact hf x
    · exact hc e
    · exact hg y
  obtain ⟨q, hq, R, hs, ht, heq⟩ :=
    real_maxFlow_minCut a b cap hcap (.inl false) (.inl true) (by simp)
  let S := Finset.univ.filter (fun x => Sum.inr (Sum.inl x) ∈ R)
  let T := Finset.univ.filter (fun y => Sum.inr (Sum.inr y) ∈ R)
  have hsplit : ∑ x, f x = (∑ x ∈ S, f x) +
      ∑ x, if Sum.inr (Sum.inl x) ∉ R then f x else 0 := by
    simp only [S, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : Sum.inr (Sum.inl x) ∈ R <;> simp [hx]
  have hcutR : ∑ x, f x ≤ networkCutCapacity a b cap R := by
    have hh := hcut S T
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.sum_filter] at hh
    rw [bipartiteNetwork_cut tail head f g c R hs ht]
    rw [hsplit]
    simpa only [S, Finset.sum_filter] using (by linarith : _)
  obtain ⟨hsource, _, hleft, hright⟩ := bipartiteNetwork_divergence tail head q
  have hqf (x : X) : q (.inl x) ≤ f x := (hq.1 (.inl x)).2
  have hqg (y : Y) : q (.inr (.inr y)) ≤ g y := (hq.1 (.inr (.inr y))).2
  have hsourceTotal : ∑ x, q (.inl x) = ∑ x, f x := by
    apply le_antisymm (Finset.sum_le_sum (fun x _ => hqf x))
    rw [← hsource]
    exact heq ▸ hcutR
  have hleftEq (x : X) :
      (∑ e, if tail e = x then q (.inr (.inl e)) else 0) = q (.inl x) := by
    have hz := hq.2 (.inr (.inl x)) (by simp) (by simp)
    rw [hleft] at hz
    linarith
  have hrightEq (y : Y) :
      (∑ e, if head e = y then q (.inr (.inl e)) else 0) = q (.inr (.inr y)) := by
    have hz := hq.2 (.inr (.inr y)) (by simp) (by simp)
    rw [hright] at hz
    linarith
  have hmiddleTotal : ∑ x, q (.inl x) = ∑ e, q (.inr (.inl e)) := by
    simp_rw [← hleftEq]
    rw [Finset.sum_comm]
    simp
  have hsinkTotal : ∑ y, q (.inr (.inr y)) = ∑ y, g y := by
    calc
      ∑ y, q (.inr (.inr y)) = ∑ e, q (.inr (.inl e)) := by
        simp_rw [← hrightEq]
        rw [Finset.sum_comm]
        simp
      _ = ∑ y, g y := by rw [← hmiddleTotal, hsourceTotal, htotal]
  have hsourceFull (x : X) : q (.inl x) = f x :=
    (Finset.sum_eq_sum_iff_of_le (fun x _ => hqf x)).mp hsourceTotal x (Finset.mem_univ x)
  have hsinkFull (y : Y) : q (.inr (.inr y)) = g y :=
    (Finset.sum_eq_sum_iff_of_le (fun y _ => hqg y)).mp hsinkTotal y (Finset.mem_univ y)
  exact ⟨fun e => q (.inr (.inl e)), fun e => hq.1 (.inr (.inl e)),
    fun x => (hleftEq x).trans (hsourceFull x),
    fun y => (hrightEq y).trans (hsinkFull y)⟩

theorem bipartite_fractionalDegrees_cutNecessary
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (c q : E → ℝ)
    (f : X → ℝ) (g : Y → ℝ) (hq : CapacityBounded c q)
    (hleft : ∀ x, (∑ e, if tail e = x then q e else 0) = f x)
    (hright : ∀ y, (∑ e, if head e = y then q e else 0) = g y)
    (S : Finset X) (T : Finset Y) :
    ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
      ∑ e, if tail e ∈ S ∧ head e ∉ T then c e else 0 := by
  have hs : ∑ x ∈ S, f x = ∑ e, if tail e ∈ S then q e else 0 := by
    simp_rw [← hleft]
    rw [Finset.sum_comm]
    simp
  have ht : ∑ y ∈ T, g y = ∑ e, if head e ∈ T then q e else 0 := by
    simp_rw [← hright]
    rw [Finset.sum_comm]
    simp
  rw [hs, ht, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases hx : tail e ∈ S <;> by_cases hy : head e ∈ T <;> simp [hx, hy]
  · exact (hq e).2
  · exact (hq e).1

theorem bipartite_fractionalDegrees_iff
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (c : E → ℝ)
    (f : X → ℝ) (g : Y → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y)
    (htotal : ∑ x, f x = ∑ y, g y) :
    (∃ q : E → ℝ, CapacityBounded c q ∧
      (∀ x, (∑ e, if tail e = x then q e else 0) = f x) ∧
      (∀ y, (∑ e, if head e = y then q e else 0) = g y)) ↔
    (∀ S : Finset X, ∀ T : Finset Y,
      ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
        ∑ e, if tail e ∈ S ∧ head e ∉ T then c e else 0) := by
  constructor
  · rintro ⟨q, hq, hleft, hright⟩ S T
    exact bipartite_fractionalDegrees_cutNecessary tail head c q f g hq hleft hright S T
  · exact bipartite_fractionalDegrees tail head c f g hc hf hg htotal

/-- The fractional conclusion of the normalized-demand lemma, with the
original part sizes and real demands. The lower demand estimates in the
manuscript imply nonnegativity; only the displayed upper estimates are
needed in the cut calculation. -/
theorem bipartite_nearUniformFractionalDegrees
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (f : X → ℝ) (g : Y → ℝ)
    {δ δ₀ M h : ℝ}
    (ha : 0 < Fintype.card X) (hb : 0 < Fintype.card Y)
    (hδ : 0 ≤ δ) (hδ₀ : δ ≤ δ₀) (hδsmall : δ₀ < 1 / 4)
    (hM : 0 ≤ M)
    (hMC : M ≤ h * Fintype.card X * Fintype.card Y / 2)
    (hftotal : ∑ x, f x = M) (hgtotal : ∑ y, g y = M)
    (hfnonneg : ∀ x, 0 ≤ f x) (hgnonneg : ∀ y, 0 ≤ g y)
    (hf : ∀ x, f x ≤ (1 + δ) * M / Fintype.card X)
    (hg : ∀ y, g y ≤ (1 + δ) * M / Fintype.card Y)
    (hlarge : ∀ (S : Finset X) (T : Finset Y),
      1 - 2 * δ₀ < (S.card : ℝ) / Fintype.card X + (T.card : ℝ) / Fintype.card Y →
      h * Fintype.card X * Fintype.card Y *
          min ((S.card : ℝ) / Fintype.card X) ((T.card : ℝ) / Fintype.card Y) ≤
        ((Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ T)).card : ℝ)) :
    ∃ q : E → ℝ, (∀ e, q e ∈ Set.Icc 0 1) ∧
      (∀ x, (∑ e, if tail e = x then q e else 0) = f x) ∧
      (∀ y, (∑ e, if head e = y then q e else 0) = g y) := by
  classical
  apply bipartite_fractionalDegrees tail head (fun _ => 1) f g
    (fun _ => zero_le_one) hfnonneg hgnonneg (hftotal.trans hgtotal.symm)
  intro S T
  let U := Tᶜ
  have hFs : ∑ x ∈ S, f x ≤ M := by
    rw [← hftotal]
    exact Finset.sum_le_univ_sum_of_nonneg hfnonneg
  have hFt : ∑ y ∈ U, g y ≤ M := by
    rw [← hgtotal]
    exact Finset.sum_le_univ_sum_of_nonneg hgnonneg
  have hFsbound : ∑ x ∈ S, f x ≤
      (1 + δ) * M * ((S.card : ℝ) / Fintype.card X) := by
    calc
      _ ≤ ∑ _ ∈ S, (1 + δ) * M / Fintype.card X :=
        Finset.sum_le_sum (fun x _ => hf x)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hFtbound : ∑ y ∈ U, g y ≤
      (1 + δ) * M * ((U.card : ℝ) / Fintype.card Y) := by
    calc
      _ ≤ ∑ _ ∈ U, (1 + δ) * M / Fintype.card Y :=
        Finset.sum_le_sum (fun y _ => hg y)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hdeficit := normalizedDemand_cut hδ hδ₀ hδsmall hM
    (show 2 * M ≤ h * Fintype.card X * Fintype.card Y by linarith)
    (div_nonneg (Nat.cast_nonneg S.card) (Nat.cast_pos.mpr ha).le)
    (div_nonneg (Nat.cast_nonneg U.card) (Nat.cast_pos.mpr hb).le)
    hFs hFt hFsbound hFtbound
    (Nat.cast_nonneg (Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ U)).card)
    (hlarge S U)
  have hsum : (∑ y ∈ T, g y) + (∑ y ∈ U, g y) = M := by
    rw [show U = Tᶜ from rfl, Finset.sum_add_sum_compl, hgtotal]
  have he : ((Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ U)).card : ℝ) =
      ∑ e, if tail e ∈ S ∧ head e ∉ T then (1 : ℝ) else 0 := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, U, Finset.mem_compl]
  rw [he] at hdeficit
  linarith

end Oberwolfach
