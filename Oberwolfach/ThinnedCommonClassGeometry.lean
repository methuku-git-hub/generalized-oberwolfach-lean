module

public import Oberwolfach.ThinnedCommonClassCounts
public import Oberwolfach.RawMarkedSpokeDisjointness
public import Oberwolfach.PermutationNeighbourCounts
public import Oberwolfach.RawMarkedNeighbourhoodEvents
public import Oberwolfach.SampledNeighbourDensity

@[expose] public section

/-! Converting fixed-domain common-class estimates to graph neighbourhoods.
The roots range over the whole ambient graph, and permutation-image
neighbourhoods use inverse images of fixed neighbourhoods. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def thinnedCommonClass (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color) (u u' : U)
    (σ : ThinnedMarkedOutcome V U Γ Color) (b : Bool) : Finset V :=
  Finset.univ.filter (fun v=>thinnedMarkedSpokes π d g j u u' σ b v ())

theorem thinnedCommonClass_disjoint (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d)
    (g : Γ) (j : Color) (u u' : U) (σ : ThinnedMarkedOutcome V U Γ Color) :
    Disjoint (thinnedCommonClass π d g j u u' σ false) (thinnedCommonClass π d g j u u' σ true) ∧
    Disjoint (thinnedCommonClass π d g j u u' σ false) ((thinnedCommonClass π d g j u u' σ true).image π) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro v h₀ hK
    exact rawMarkedSpokes_disjoint π d (fun e=>σ (Sum.inl (Sum.inr e))) g j v u
      ⟨(Finset.mem_filter.mp h₀).2.1,(Finset.mem_filter.mp hK).2.1⟩
  · apply Finset.disjoint_left.mpr
    intro v h₀ hK
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hK
    exact rawMarkedSpokes_successor_disjoint π d hd (fun e=>σ (Sum.inl (Sum.inr e))) g j w u
      ⟨(Finset.mem_filter.mp h₀).2.1,(Finset.mem_filter.mp hw).2.1⟩

theorem thinnedCommonClass_domain_counts (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (g : Γ) (j : Color) (u u' : U) (σ : ThinnedMarkedOutcome V U Γ Color)
    (b : Bool) (a t : ℝ)
    (hc : ∀ z : Option (V⊕V),
      |thinnedCommonClassCount π d g j u u' b (markedReferenceDomain P π z) σ-
        a*(markedReferenceDomain P π z).card|<t) :
    let T := thinnedCommonClass π d g j u u' σ b
    (|(T.card:ℝ)-a*Fintype.card V|<t) ∧
    (∀ x : V,|((P.neighborFinset x∩T).card:ℝ)-a*P.degree x|<t) ∧
    (∀ x : V,|((P.neighborFinset x∩T.image π).card:ℝ)-a*P.degree x|<t) := by
  intro T
  simp_rw [thinnedCommonClassCount_card] at hc
  refine ⟨?_,?_,?_⟩
  · simpa only [markedReferenceDomain,Finset.card_univ,T,thinnedCommonClass] using hc none
  · intro x
    have hfilter : (P.neighborFinset x).filter (fun v=>thinnedMarkedSpokes π d g j u u' σ b v ())=
        P.neighborFinset x∩T := by
      ext v
      simp only [T,thinnedCommonClass,Finset.mem_filter,Finset.mem_inter,Finset.mem_univ,true_and]
    simpa only [markedReferenceDomain,hfilter,SimpleGraph.card_neighborFinset_eq_degree] using hc (some (Sum.inl x))
  · intro x
    have hfilter : (markedReferenceDomain P π (some (Sum.inr x))).filter
        (fun v=>thinnedMarkedSpokes π d g j u u' σ b v ())=T.filter (fun v=>P.Adj x (π v)) := by
      ext v
      simp only [markedReferenceDomain,T,thinnedCommonClass,Finset.mem_filter,Finset.mem_univ,true_and,and_comm]
    have hi := hc (some (Sum.inr x))
    rw [hfilter,permutation_neighbour_filter_card] at hi
    simpa only [markedReferenceDomain,permutation_neighbour_domain_card] using hi

theorem thinnedCommonClass_dense (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (g : Γ) (j : Color) (u u' : U) (σ : ThinnedMarkedOutcome V U Γ Color)
    (b : Bool) (α a astar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hastar : 0<astar) (ha : astar≤a)
    (hP : ∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ))
    (hc : ∀ z : Option (V⊕V),
      |thinnedCommonClassCount π d g j u u' b (markedReferenceDomain P π z) σ-
        a*(markedReferenceDomain P π z).card|<min (astar/4) (α*astar/8)*Fintype.card V) :
    let T := thinnedCommonClass π d g j u u' σ b
    (astar/2*Fintype.card V≤(T.card:ℝ)) ∧
    (∀ x : V,(1/2+α/2)*T.card≤((P.neighborFinset x∩T).card:ℝ)) ∧
    (∀ x : V,(1/2+α/2)*T.card≤((P.neighborFinset x∩T.image π).card:ℝ)) := by
  intro T
  let ε := min (astar/4) (α*astar/8)
  have he : 0<ε := lt_min (by positivity) (by positivity)
  have hn : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  have ha0 : 0<a := hastar.trans_le ha
  have han := mul_le_mul_of_nonneg_right ha hn
  have hesize : ε*Fintype.card V≤a*Fintype.card V/2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_left (astar/4) (α*astar/8)) hn
    dsimp [ε]
    nlinarith only [h,han,mul_nonneg hastar.le hn]
  have heerror : ε*Fintype.card V≤α*a*Fintype.card V/4 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (astar/4) (α*astar/8)) hn
    have hh := mul_le_mul_of_nonneg_left han hα.le
    dsimp [ε]
    nlinarith only [h,hh,mul_nonneg hα.le (mul_nonneg hastar.le hn)]
  have hcounts := thinnedCommonClass_domain_counts P π d g j u u' σ b a (ε*Fintype.card V) hc
  refine ⟨?_,?_,?_⟩
  · have hlo := (abs_lt.mp hcounts.1).1
    have h := mul_le_mul_of_nonneg_right (min_le_left (astar/4) (α*astar/8)) hn
    dsimp [ε] at hlo
    nlinarith only [hlo,h,han,mul_nonneg hastar.le hn]
  · intro x
    exact (sampled_neighbour_density (Fintype.card V:ℝ) a (1/2) α (ε*Fintype.card V)
      T.card (P.degree x) ((P.neighborFinset x∩T).card) hn ha0.le hα (by positivity)
      (by linarith) (by positivity) hesize heerror hcounts.1.le (hP x) (hcounts.2.1 x).le).2
  · intro x
    exact (sampled_neighbour_density (Fintype.card V:ℝ) a (1/2) α (ε*Fintype.card V)
      T.card (P.degree x) ((P.neighborFinset x∩T.image π).card) hn ha0.le hα (by positivity)
      (by linarith) (by positivity) hesize heerror hcounts.1.le (hP x) (hcounts.2.2 x).le).2

end Oberwolfach
