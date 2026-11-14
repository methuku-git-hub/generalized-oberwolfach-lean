module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-!
Finite networks with real capacities. Edges are indexed independently of
their endpoints, so parallel arcs and opposite arcs are not identified.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def vertexDifference {V : Type*} [DecidableEq V] (x y v : V) : ℝ :=
  (if x = v then 1 else 0) - (if y = v then 1 else 0)

def flowDivergence {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (f : E → ℝ) (v : V) : ℝ :=
  ∑ e, f e * vertexDifference (tail e) (head e) v

def CapacityBounded {E : Type*} (c f : E → ℝ) : Prop :=
  ∀ e, 0 ≤ f e ∧ f e ≤ c e

def IsNetworkFlow {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (c : E → ℝ) (s t : V) (f : E → ℝ) : Prop :=
  CapacityBounded c f ∧ ∀ v, v ≠ s → v ≠ t → flowDivergence tail head f v = 0

/-- A change of flow that transfers a positive amount from `x` to `y`.
The base flow remains fixed in this relation. -/
def FlowTransfer {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (c f : E → ℝ) (x y : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ g : E → ℝ, CapacityBounded c g ∧
    ∀ v, flowDivergence tail head g v =
      flowDivergence tail head f v + ε * vertexDifference x y v

theorem vertexDifference_trans {V : Type*} [DecidableEq V] (x y z v : V) :
    vertexDifference x z v + vertexDifference z y v = vertexDifference x y v := by
  unfold vertexDifference
  ring

theorem flowDivergence_linear
    {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (f g : E → ℝ) (a b : ℝ) (v : V) :
    flowDivergence tail head (fun e => a * f e + b * g e) v =
      a * flowDivergence tail head f v + b * flowDivergence tail head g v := by
  simp only [flowDivergence, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

theorem capacityBounded_convex
    {E : Type*} (c f g : E → ℝ) (hf : CapacityBounded c f)
    (hg : CapacityBounded c g) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    CapacityBounded c (fun e => a * f e + b * g e) := by
  intro e
  constructor
  · exact add_nonneg (mul_nonneg ha (hf e).1) (mul_nonneg hb (hg e).1)
  · calc
      a * f e + b * g e ≤ a * c e + b * c e :=
        add_le_add (mul_le_mul_of_nonneg_left (hf e).2 ha)
          (mul_le_mul_of_nonneg_left (hg e).2 hb)
      _ = c e := by rw [← add_mul, hab, one_mul]

theorem flowTransfer_refl
    {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (c f : E → ℝ) (hf : CapacityBounded c f) (x : V) :
    FlowTransfer tail head c f x x := by
  refine ⟨1, by norm_num, f, hf, ?_⟩
  intro v
  simp [vertexDifference]

/-- Two transfers from the same base flow can be combined by a convex
combination. The intermediate divergence cancels exactly. -/
theorem flowTransfer_trans
    {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (c f : E → ℝ) {x z y : V}
    (hx : FlowTransfer tail head c f x z)
    (hy : FlowTransfer tail head c f z y) :
    FlowTransfer tail head c f x y := by
  obtain ⟨u, hu, g, hg, hdivg⟩ := hx
  obtain ⟨w, hw, h, hh, hdivh⟩ := hy
  have hsum : 0 < u + w := add_pos hu hw
  let a := w / (u + w)
  let b := u / (u + w)
  have ha : 0 ≤ a := le_of_lt (div_pos hw hsum)
  have hb : 0 ≤ b := le_of_lt (div_pos hu hsum)
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  refine ⟨u * w / (u + w), div_pos (mul_pos hu hw) hsum,
    (fun e => a * g e + b * h e), capacityBounded_convex c g h hg hh ha hb hab, ?_⟩
  intro v
  rw [flowDivergence_linear, hdivg, hdivh]
  have hd := vertexDifference_trans x y z v
  dsimp [a, b]
  rw [← hd]
  field_simp
  ring

theorem flowDivergence_add_single
    {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (tail head : E → V) (f : E → ℝ) (e : E) (ε : ℝ) (v : V) :
    flowDivergence tail head (fun j => f j + if j = e then ε else 0) v =
      flowDivergence tail head f v + ε * vertexDifference (tail e) (head e) v := by
  simp only [flowDivergence, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp

theorem flowTransfer_forward
    {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (tail head : E → V) (c f : E → ℝ) (hf : CapacityBounded c f)
    (e : E) (he : f e < c e) :
    FlowTransfer tail head c f (tail e) (head e) := by
  refine ⟨c e - f e, sub_pos.mpr he, (fun j => f j + if j = e then c e - f e else 0),
    ?_, fun v => flowDivergence_add_single tail head f e (c e - f e) v⟩
  intro j
  by_cases hj : j = e
  · subst j
    simp only [ite_true, add_sub_cancel]
    exact ⟨(hf e).1.trans (hf e).2, le_refl _⟩
  · simpa [hj] using hf j

theorem flowTransfer_backward
    {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (tail head : E → V) (c f : E → ℝ) (hf : CapacityBounded c f)
    (e : E) (he : 0 < f e) :
    FlowTransfer tail head c f (head e) (tail e) := by
  refine ⟨f e, he, (fun j => f j + if j = e then -f e else 0), ?_, ?_⟩
  · intro j
    by_cases hj : j = e
    · subst j
      simp only [ite_true, add_neg_cancel]
      exact ⟨le_refl _, (hf e).1.trans (hf e).2⟩
    · simpa [hj] using hf j
  · intro v
    rw [flowDivergence_add_single]
    unfold vertexDifference
    ring

theorem flowDivergence_sum_cut
    {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (f : E → ℝ) (S : Finset V) :
    ∑ v ∈ S, flowDivergence tail head f v =
      ∑ e, f e * ((if tail e ∈ S then (1 : ℝ) else 0) -
        (if head e ∈ S then 1 else 0)) := by
  unfold flowDivergence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum]
  simp [vertexDifference, Finset.sum_sub_distrib]

def networkCutCapacity
    {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (c : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e, if tail e ∈ S ∧ head e ∉ S then c e else 0

theorem networkFlow_cut_bound
    {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (c f : E → ℝ) (s t : V)
    (hf : IsNetworkFlow tail head c s t f)
    (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    flowDivergence tail head f s ≤ networkCutCapacity tail head c S := by
  have hdiv : ∑ v ∈ S, flowDivergence tail head f v =
      flowDivergence tail head f s := by
    apply Finset.sum_eq_single_of_mem s hs
    intro v hv hvs
    exact hf.2 v hvs (by intro hvt; subst v; exact ht hv)
  rw [← hdiv, flowDivergence_sum_cut]
  apply Finset.sum_le_sum
  intro e _
  by_cases hx : tail e ∈ S <;> by_cases hy : head e ∈ S <;>
    simp [hx, hy]
  · exact (hf.1 e).2
  · exact (hf.1 e).1

theorem exists_maximum_real_flow
    {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) (s t : V) :
    ∃ f : E → ℝ, IsNetworkFlow tail head c s t f ∧
      ∀ g, IsNetworkFlow tail head c s t g →
        flowDivergence tail head g s ≤ flowDivergence tail head f s := by
  let K : Set (E → ℝ) := {f | IsNetworkFlow tail head c s t f}
  have hcont (v : V) : Continuous (fun f : E → ℝ => flowDivergence tail head f v) := by
    unfold flowDivergence
    fun_prop
  have hclosed : IsClosed K := by
    change IsClosed {f | (∀ e, 0 ≤ f e ∧ f e ≤ c e) ∧
      ∀ v, v ≠ s → v ≠ t → flowDivergence tail head f v = 0}
    simp only [Set.ofPred_and, Set.ofPred_forall]
    apply IsClosed.inter
    · exact isClosed_iInter fun e =>
        (isClosed_le continuous_const (continuous_apply e)).inter
          (isClosed_le (continuous_apply e) continuous_const)
    · exact isClosed_iInter fun v => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_eq (hcont v) continuous_const
  have hcompact : IsCompact K :=
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : E => (0 : ℝ)) c)).of_isClosed_subset
      hclosed (by
        intro f hf
        exact ⟨fun e => (hf.1 e).1, fun e => (hf.1 e).2⟩)
  have hzero : (fun _ : E => (0 : ℝ)) ∈ K := by
    refine ⟨fun e => ⟨le_refl _, hc e⟩, ?_⟩
    intro v _ _
    simp [flowDivergence]
  obtain ⟨f, hf, hmax⟩ := hcompact.exists_isMaxOn ⟨_, hzero⟩ (hcont s).continuousOn
  exact ⟨f, hf, fun g hg => hmax hg⟩

/-- A maximum real flow has a cut of equal capacity. There is no rationality
assumption on the capacities and no termination claim for augmenting paths. -/
theorem real_maxFlow_minCut
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (tail head : E → V) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (s t : V) (hst : s ≠ t) :
    ∃ f : E → ℝ, IsNetworkFlow tail head c s t f ∧
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧
        flowDivergence tail head f s = networkCutCapacity tail head c S := by
  classical
  obtain ⟨f, hf, hmax⟩ := exists_maximum_real_flow tail head c hc s t
  let S := Finset.univ.filter (FlowTransfer tail head c f s)
  have hs : s ∈ S := by
    simpa [S] using flowTransfer_refl tail head c f hf.1 s
  have ht : t ∉ S := by
    intro ht
    obtain ⟨ε, hε, g, hg, hd⟩ : FlowTransfer tail head c f s t := by
      simpa [S] using ht
    have hgf : IsNetworkFlow tail head c s t g := by
      refine ⟨hg, fun v hvs hvt => ?_⟩
      rw [hd, hf.2 v hvs hvt]
      simp [vertexDifference, Ne.symm hvs, Ne.symm hvt]
    have hle := hmax g hgf
    have hds := hd s
    simp only [vertexDifference, ite_true, Ne.symm hst, ite_false, sub_zero, mul_one] at hds
    linarith
  have hout (e : E) (hx : tail e ∈ S) (hy : head e ∉ S) : f e = c e := by
    apply le_antisymm (hf.1 e).2
    by_contra hn
    have hlt : f e < c e := lt_of_not_ge hn
    have hx' : FlowTransfer tail head c f s (tail e) := by simpa [S] using hx
    have hy' := flowTransfer_trans tail head c f hx'
      (flowTransfer_forward tail head c f hf.1 e hlt)
    exact hy (by simpa [S] using hy')
  have hin (e : E) (hx : tail e ∉ S) (hy : head e ∈ S) : f e = 0 := by
    apply le_antisymm _ (hf.1 e).1
    by_contra hn
    have hlt : 0 < f e := lt_of_not_ge hn
    have hy' : FlowTransfer tail head c f s (head e) := by simpa [S] using hy
    have hx' := flowTransfer_trans tail head c f hy'
      (flowTransfer_backward tail head c f hf.1 e hlt)
    exact hx (by simpa [S] using hx')
  refine ⟨f, hf, S, hs, ht, ?_⟩
  have hdiv : ∑ v ∈ S, flowDivergence tail head f v =
      flowDivergence tail head f s := by
    apply Finset.sum_eq_single_of_mem s hs
    intro v hv hvs
    exact hf.2 v hvs (by intro hvt; subst v; exact ht hv)
  rw [← hdiv, flowDivergence_sum_cut]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hx : tail e ∈ S <;> by_cases hy : head e ∈ S <;> simp [hx, hy]
  · exact hout e hx hy
  · exact hin e hx hy

end Oberwolfach
