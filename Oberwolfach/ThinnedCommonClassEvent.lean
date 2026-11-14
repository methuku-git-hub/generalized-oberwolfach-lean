module

public import Oberwolfach.ThinnedCommonClassGeometry

@[expose] public section

/-! A uniform order threshold for the common classes of a fixed hub pair.
The threshold precedes the original density arrays and thinning density;
the only density input is a fixed positive lower bound for both classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem thinnedCommonClass_dense_event
    (α astar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hastar : 0<astar)
    (d Q : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U),u≠u' →
      astar≤q u g*q u' g → astar≤s u j*s u' j*θ →
    1-1/(Fintype.card V:ℝ)^Q≤
      (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability
        (fun σ=>let T:=thinnedCommonClass π d g j u u' σ
          Disjoint (T false) (T true) ∧ Disjoint (T false) ((T true).image π) ∧
          ∀ b,(astar/2*Fintype.card V≤((T b).card:ℝ)) ∧
            (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩T b).card:ℝ)) ∧
            (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩(T b).image π).card:ℝ))) := by
  let ε := min (astar/4) (α*astar/8)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := linear_deviation_failure_eventually_small 6 ((16*(d:ℝ)+14)^2) ε (by positivity) hε 1 Q
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN P π hP hnoshort p k hp hk hphys q hq hQ s hs hS θ hθ hθ1 g j u u' hu hqmin hsmin
  have hn : 0<Fintype.card V := by omega
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hh := thinnedCommonClassCount_common_event π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
    θ hθ hθ1 g j u u' hu (markedReferenceDomain P π) hn (ε*Fintype.card V) (by positivity)
  have hcard : (2*Fintype.card (Option (V⊕V)):ℝ)≤6*(Fintype.card V:ℝ)^1 := by
    simp only [Fintype.card_option,Fintype.card_sum,Nat.cast_add,Nat.cast_one,pow_one]
    have hn1 : (1:ℝ)≤Fintype.card V := by exact_mod_cast hn
    linarith
  have ht := hN (Fintype.card V) (by omega) (2*Fintype.card (Option (V⊕V)))
    ((16*(d:ℝ)+14)^2*Fintype.card V) (by positivity) hcard (by positivity) le_rfl
  apply ((sub_le_sub_left ht 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨(thinnedCommonClass_disjoint π d (by omega) g j u u' σ).1,
    (thinnedCommonClass_disjoint π d (by omega) g j u u' σ).2,?_⟩
  intro b
  exact thinnedCommonClass_dense P π d g j u u' σ b α
    (if b then q u g*q u' g else s u j*s u' j*θ) astar hα hα1 hastar
    (by cases b <;> assumption) hP (hσ b)

end Oberwolfach
