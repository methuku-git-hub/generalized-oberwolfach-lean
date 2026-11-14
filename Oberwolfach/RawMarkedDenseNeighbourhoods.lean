module

public import Oberwolfach.RawMarkedNeighbourhoodGraphs
public import Oberwolfach.SampledNeighbourDensity

@[expose] public section

/-! Both random spoke-intersection classes have dense neighbourhoods at
every ambient root, also after applying the successor permutation.
The error is selected before the interval length and actual densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarkedNeighbourhood_dense_event
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → pstar≤s₀ → pstar≤t₀ →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ (b : Bool) (u : Fin 2→U),Function.Injective u →
          let T := Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))
          (pstar^2/2*Fintype.card V≤(T.card:ℝ)) ∧
          (∀ x : V,(1/2+α/2)*T.card≤((P.neighborFinset x∩T).card:ℝ)) ∧
          (∀ x : V,(1/2+α/2)*T.card≤((P.neighborFinset x∩T.image π).card:ℝ))) := by
  let ε := min (pstar^2/4) (α*pstar^2/8)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := rawMarkedNeighbourhood_graph_event ε hε 2 d q₀ (by omega) hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hmhi P hP π q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo hnoshort
  have hh := hN V U Γ Color hn hmhi P π q hq hQ s hs hS g j s₀ t₀ hg hj hnoshort
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ b u hu
  let T := Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))
  let a := if b then t₀ else s₀
  have ha : pstar≤a := by cases b <;> assumption
  have ha0 : 0<a := hpstar.trans_le ha
  have hsquare : pstar^2≤a^2 := by nlinarith only [ha,hpstar]
  have hn0 : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  have hsqn := mul_le_mul_of_nonneg_right hsquare hn0
  have hesize : ε*Fintype.card V≤a^2*Fintype.card V/2 := by
    have he := mul_le_mul_of_nonneg_right (min_le_left (pstar^2/4) (α*pstar^2/8)) hn0
    dsimp [ε]
    nlinarith only [he,hsqn,mul_nonneg (sq_nonneg pstar) hn0]
  have heerror : ε*Fintype.card V≤α*a^2*Fintype.card V/4 := by
    have he := mul_le_mul_of_nonneg_right (min_le_right (pstar^2/4) (α*pstar^2/8)) hn0
    have hh := mul_le_mul_of_nonneg_left hsqn hα.le
    dsimp [ε]
    nlinarith only [he,hh,mul_nonneg hα.le (mul_nonneg (sq_nonneg pstar) hn0)]
  have hcounts := hσ b u hu
  change (|(T.card:ℝ)-a^2*Fintype.card V|<ε*Fintype.card V) ∧
    (∀ x : V,|((P.neighborFinset x∩T).card:ℝ)-a^2*P.degree x|<ε*Fintype.card V) ∧
    (∀ x : V,|((P.neighborFinset x∩T.image π).card:ℝ)-a^2*P.degree x|<ε*Fintype.card V) at hcounts
  refine ⟨?_,?_,?_⟩
  · have hlo := (abs_lt.mp hcounts.1).1
    have he := mul_le_mul_of_nonneg_right (min_le_left (pstar^2/4) (α*pstar^2/8)) hn0
    dsimp [ε] at hlo
    nlinarith only [hlo,he,hsqn,mul_nonneg (sq_nonneg pstar) hn0]
  · intro x
    exact (sampled_neighbour_density (Fintype.card V:ℝ) (a^2) (1/2) α
      (ε*Fintype.card V) T.card (P.degree x) ((P.neighborFinset x∩T).card)
      hn0 (sq_nonneg a) hα (by positivity) (by linarith) (by positivity)
      hesize heerror hcounts.1.le (hP x) (hcounts.2.1 x).le).2
  · intro x
    exact (sampled_neighbour_density (Fintype.card V:ℝ) (a^2) (1/2) α
      (ε*Fintype.card V) T.card (P.degree x) ((P.neighborFinset x∩T.image π).card)
      hn0 (sq_nonneg a) hα (by positivity) (by linarith) (by positivity)
      hesize heerror hcounts.1.le (hP x) (hcounts.2.2 x).le).2

end Oberwolfach
