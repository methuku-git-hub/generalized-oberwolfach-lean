module

public import Oberwolfach.GoodPlacementEvents
public import Oberwolfach.ExponentialMarkedDenseNeighbourhoods
public import Oberwolfach.RawMarkedSpokeDisjointness
public import Oberwolfach.ExponentialMarkedHubs
public import Oberwolfach.PolynomialExponentialErrors

@[expose] public section

/-! The first exposure in the marked configuration argument: all compatible
hub counts and both dense spoke-intersection classes hold on one event.
The class disjointness is deterministic, and every graph-neighbourhood
estimate ranges over the full vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedFirstExponent (m : ℕ) (α sstar tstar ω : ℝ) (d : ℕ) : ℝ :=
  min (2*(ω*tstar*sstar^m/2)^2/((4*(d:ℝ)+3)^2*((m:ℝ)+1)))
    ((min ((min sstar tstar)^2/4) (α*(min sstar tstar)^2/8))^2/(4*(d:ℝ)+3)^2)

theorem markedFirstExponent_pos (m : ℕ) (α sstar tstar ω : ℝ) (d : ℕ)
    (hα : 0<α) (hsstar : 0<sstar) (htstar : 0<tstar) (hω : 0<ω) :
    0<markedFirstExponent m α sstar tstar ω d := by
  unfold markedFirstExponent
  positivity

theorem rawMarked_first_exponential_event
    (m : ℕ) (α sstar tstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hω : 0<ω)
    (d : ℕ) (hd : 2≤d) :
    ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      0<Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → tstar≤t₀ →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    1-14*(Fintype.card V:ℝ)^(m+4)*Real.exp (-markedFirstExponent m α sstar tstar ω d*Fintype.card V)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>
          (∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
            (ω*tstar*sstar^m/2)*Fintype.card V≤
              ((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ)) ∧
          (∀ (u : Fin 2→U),Function.Injective u →
            let T := fun b : Bool=>Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))
            Disjoint (T false) (T true) ∧ Disjoint (T false) ((T true).image π) ∧
            ∀ b : Bool,
              ((min sstar tstar)^2/2*Fintype.card V≤((T b).card:ℝ)) ∧
              (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩T b).card:ℝ)) ∧
              (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩(T b).image π).card:ℝ)))) := by
  let pstar := min sstar tstar
  have hpstar : 0<pstar := lt_min hsstar htstar
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P hP π q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo hnoshort
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hh := rawMarkedHubs_exponential_probability m sstar tstar ω hsstar htstar hω d hd V U Γ Color hn hmlo hmhi π q hq hQ s hs hS g j
    (by intro u;rw [hg];exact htlo) (by intro u;rw [hj];exact hslo) hnoshort
  have hdense := rawMarkedNeighbourhood_exponential_dense_event α pstar hα hα1 hpstar d hd V U Γ Color hn hmhi P hP π q hq hQ s hs hS g j s₀ t₀ hg hj
    ((min_le_left _ _).trans hslo) ((min_le_right _ _).trans htlo) hnoshort
  let cH := 2*(ω*tstar*sstar^m/2)^2/((4*(d:ℝ)+3)^2*((m:ℝ)+1))
  let cD := (min (pstar^2/4) (α*pstar^2/8))^2/(4*(d:ℝ)+3)^2
  let errH := 2*(n:ℝ)^(m+1)*Real.exp (-cH*n)
  let errD := 12*(n:ℝ)^3*Real.exp (-cD*n)
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
      (ω*tstar*sstar^m/2)*Fintype.card V≤((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ))
    _ errD hdense
  have hbase := (sub_le_sub_right hh errD).trans hjoint
  have hsum := two_polynomial_exponential_errors_le (n:ℝ) 2 12 cH cD (m+1) 3 (m+4)
    (by exact_mod_cast hn) (by norm_num) (by norm_num) (by omega) (by omega)
  have hbound : 1-14*(n:ℝ)^(m+4)*Real.exp (-markedFirstExponent m α sstar tstar ω d*n)≤1-errH-errD := by
    change errH+errD≤(2+12)*(n:ℝ)^(m+4)*Real.exp (-markedFirstExponent m α sstar tstar ω d*n) at hsum
    linarith only [hsum]
  apply (hbound.trans hbase).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨hσ.1,?_⟩
  intro u hu
  have hdisj := rawMarkedSpokeClasses_disjoint π d (by omega) σ g j u
  exact ⟨hdisj.1,hdisj.2,fun b=>hσ.2 b u hu⟩

end Oberwolfach
