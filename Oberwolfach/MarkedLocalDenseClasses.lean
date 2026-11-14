module

public import Oberwolfach.MarkedLocalNeighbourGraphs
public import Oberwolfach.SampledNeighbourDensity
public import Oberwolfach.RawMarkedSpokeDisjointness

@[expose] public section

/-! Dense one-hub classes on the inner domain. The degree hypothesis is
explicit at every ambient root, including roots outside that domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem rawMarkedLocal_classes_disjoint (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (j : Color) (A : Finset V) (u : U) :
    Disjoint (rawMarkedLocalClass π d σ g j A false u) (rawMarkedLocalClass π d σ g j A true u) ∧
      Disjoint (rawMarkedLocalClass π d σ g j A false u) ((rawMarkedLocalClass π d σ g j A true u).image π) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact rawMarkedSpokes_disjoint π d σ g j x u ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    exact rawMarkedSpokes_successor_disjoint π d hd σ g j v u ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hv).2⟩

theorem rawMarkedLocal_dense_event (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (P : SimpleGraph V) (A : Finset V) (hA : A.Nonempty) (hInv : ∀ x,π x∈A ↔ x∈A)
    (K α pstar : ℝ) (hK : 1≤K) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar)
    (hV : (Fintype.card V:ℝ)≤K*A.card) (hU : (Fintype.card U:ℝ)≤K*A.card)
    (hP : ∀ x,(1/2+α)*A.card≤((P.neighborFinset x∩A).card:ℝ))
    (g : Γ) (j : Color) (s₀ t₀ : ℝ) (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (hslo : pstar≤s₀) (htlo : pstar≤t₀) :
    let ε := min (pstar/4) (α*pstar/8)
    1-12*K^2*(A.card:ℝ)^2*Real.exp (-(2*ε^2/((4*(d:ℝ)+3)^2*K))*A.card)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ u : U,
          let T := fun b=>rawMarkedLocalClass π d σ g j A b u
          Disjoint (T false) (T true) ∧ Disjoint (T false) ((T true).image π) ∧
          ∀ b : Bool,(pstar/2*A.card≤((T b).card:ℝ)) ∧
          (∀ x,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩T b).card:ℝ)) ∧
          (∀ x,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩(T b).image π).card:ℝ))) := by
  let ε := min (pstar/4) (α*pstar/8)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  have hh := rawMarkedLocal_graph_event π d hd q hq hQ s hs hS hnoshort P A hA hInv K ε hK hε hV hU g j s₀ t₀ hg hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ u
  have hdj := rawMarkedLocal_classes_disjoint π d (by omega) σ g j A u
  refine ⟨hdj.1,hdj.2,?_⟩
  intro b
  let T := rawMarkedLocalClass π d σ g j A b u
  let a := if b then t₀ else s₀
  have ha : pstar≤a := by cases b <;> assumption
  have ha0 : 0≤a := hpstar.le.trans ha
  have hn0 : (0:ℝ)≤A.card := Nat.cast_nonneg _
  have hsize : ε*A.card≤a*A.card/2 := by
    have he := mul_le_mul_of_nonneg_right (min_le_left (pstar/4) (α*pstar/8)) hn0
    have hs := mul_le_mul_of_nonneg_right ha hn0
    dsimp [ε]
    nlinarith only [he,hs,mul_nonneg hpstar.le hn0]
  have hmargin : ε*A.card≤α*a*A.card/4 := by
    have he := mul_le_mul_of_nonneg_right (min_le_right (pstar/4) (α*pstar/8)) hn0
    have hs := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha hn0) hα.le
    dsimp [ε]
    nlinarith only [he,hs,mul_nonneg hα.le (mul_nonneg hpstar.le hn0)]
  have hc := hσ b u
  change |(T.card:ℝ)-a*A.card|<ε*A.card ∧
    (∀ x,|((P.neighborFinset x∩T).card:ℝ)-a*(P.neighborFinset x∩A).card|<ε*A.card) ∧
    (∀ x,|((P.neighborFinset x∩T.image π).card:ℝ)-a*(P.neighborFinset x∩A).card|<ε*A.card) at hc
  refine ⟨?_,?_,?_⟩
  · have hlo := (abs_lt.mp hc.1).1
    have haN := mul_le_mul_of_nonneg_right ha hn0
    linarith only [hlo,hsize,haN]
  · intro x
    exact (sampled_neighbour_density A.card a (1/2) α (ε*A.card) T.card
      (P.neighborFinset x∩A).card (P.neighborFinset x∩T).card hn0 ha0 hα (by positivity)
      (by linarith) (by positivity) hsize hmargin hc.1.le (hP x) (hc.2.1 x).le).2
  · intro x
    exact (sampled_neighbour_density A.card a (1/2) α (ε*A.card) T.card
      (P.neighborFinset x∩A).card (P.neighborFinset x∩T.image π).card hn0 ha0 hα (by positivity)
      (by linarith) (by positivity) hsize hmargin hc.1.le (hP x) (hc.2.2 x).le).2

end Oberwolfach
