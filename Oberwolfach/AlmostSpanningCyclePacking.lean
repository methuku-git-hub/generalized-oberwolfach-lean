module

public import Oberwolfach.FractionalAlmostPerfectMatching
public import Oberwolfach.CycleVertexMatchingWeights
public import Oberwolfach.PositiveOrdinaryCycleWeights
public import Oberwolfach.TwoComponentLower

@[expose] public section

/-! Actual vertex-disjoint cycle packings in almost-regular dense graphs.
The threshold and regularity tolerance are chosen before the graph. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_incidence_load_adjacency
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (a : OrdinaryCycle G r → ℝ)
    (he : ∀ e : G.edgeSet, ∑ C, a C*ordinaryCycleIncidence G r C e=1) :
    ∀ x y, (∑ C, if C.val.val.Adj x y then a C else 0)=if G.Adj x y then 1 else 0 := by
  intro x y
  by_cases hxy : G.Adj x y
  · have hh := he ⟨s(x,y),hxy⟩
    simpa only [ordinaryCycleIncidence,SimpleGraph.mem_edgeSet,mul_ite,mul_one,mul_zero,
      hxy,ite_true] using hh
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro C _
    have hn : ¬ C.val.val.Adj x y := fun h => hxy (C.property h)
    simp [hn]

theorem almost_spanning_cycle_packing
    (r : ℕ) (hr : 3≤r) (α ξ : ℝ) (hα : 0<α) (hξ : 0<ξ) (hξ1 : ξ≤1) :
    ∃ η : ℝ, 0<η ∧ ∃ N : ℕ, 0<N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], N≤Fintype.card V →
      ∀ G : SimpleGraph V,
        (∀ v, (cycleThreshold r+α)*Fintype.card V≤(G.degree v : ℝ)) →
      ∀ d : ℝ, (∀ v, (1-η)*d≤(G.degree v : ℝ) ∧ (G.degree v : ℝ)≤d) →
      ∃ M : Finset (OrdinaryCycle G r),
        (M : Set (OrdinaryCycle G r)).Pairwise (fun C D =>
          Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r D)) ∧
        (1-ξ)*Fintype.card V≤((M.biUnion (ordinaryCycleVertices G r)).card : ℝ) := by
  let μ := HadwigerLean.Theorem2.matchingMu r ξ
  have hμ : 0<μ := by
    dsimp [μ,HadwigerLean.Theorem2.matchingMu]
    have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
    positivity
  obtain ⟨c,C,hc,hC,N₀,hN₀,hweights⟩ := positive_ordinary_fractional_cycle_weights r hr α hα
  let N := max N₀ ⌈16*(r : ℝ)^2*C/μ⌉₊
  refine ⟨μ/4,by positivity,N,lt_of_lt_of_le hN₀ (le_max_left _ _),?_⟩
  intro V _ _ hn G hG d hd
  have hn₀ : N₀≤Fintype.card V := (le_max_left _ _).trans hn
  have hnpos : 0<Fintype.card V := hN₀.trans_le hn₀
  have hnR : (0 : ℝ)<Fintype.card V := Nat.cast_pos.mpr hnpos
  obtain ⟨a,ha,he⟩ := hweights V hn₀ G hG
  have ha0 (A : OrdinaryCycle G r) : 0≤a A :=
    (div_nonneg hc.le (by positivity)).trans (ha A).1
  have hnlarge : 16*(r : ℝ)^2*C/μ≤(Fintype.card V : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hn : ⌈16*(r : ℝ)^2*C/μ⌉₊≤_))
  have hpairnum : 4*(r : ℝ)^2*C/(Fintype.card V : ℝ)≤μ/4 := by
    have hh := (div_le_iff₀ hμ).mp hnlarge
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  have hdhalf : (Fintype.card V : ℝ)/2≤d := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hnpos
    have ht := cycleThreshold_half_le hr
    have hg := hG v
    have hh := (hd v).2
    have hn0 : (0 : ℝ)≤Fintype.card V := hnR.le
    nlinarith [mul_nonneg hα.le hn0,mul_nonneg (sub_nonneg.mpr ht) hn0]
  obtain ⟨b,hb,hload,hpair⟩ := ordinary_cycle_vertex_matching_weights G r (by omega) hnpos
    a ha0 C hC.le (fun A => (ha A).2)
    (ordinary_cycle_incidence_load_adjacency G r a he) hdhalf hd
  exact almost_perfect_matching_of_fractional_weights (ordinaryCycleVertices G r) r (by omega)
    (ordinaryCycleVertices_card G r) ξ hξ hξ1 b hb hload
    (fun x y hxy => (hpair x y hxy).trans hpairnum)

end Oberwolfach
