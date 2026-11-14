module

public import Oberwolfach.AllCutsExponentialMargins
public import Oberwolfach.RawSelectedCutCounts

@[expose] public section

/-! Quadratic spoke-cut tests with exponential error on the original
locally dependent interval law. No independent pair model is substituted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawSelectedCutCount_quadratic_exponential_event (d : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → 0<Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Γ⊕Color),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pH : ℝ,(∀ u,Sum.elim (q u) (s u) j=pH) →
    1-2*Real.exp (-(ε^2/(4*(d:ℝ)+3)^2)*Fintype.card V)≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ X Y,|rawSelectedCutCount π d σ j X Y-pH*X.card*Y.card|<ε*(Fintype.card V:ℝ)^2) := by
  obtain ⟨N,hN1,hN⟩ := eventually_allCuts_failure_exponential (c:=2*ε^2/(4*(d:ℝ)+3)^2) (by positivity)
  refine ⟨N,hN1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hm hmhi π q hq hQ s hs hS j hnoshort pH hj
  let n := Fintype.card V
  have hnpos : 0<n := by dsimp [n];omega
  have hnreal : (0:ℝ)<n := by exact_mod_cast hnpos
  have hh := rawSelectedCutCount_all_cuts π d hd q hq hQ s hs hS hnoshort hnpos hm hmhi
    j pH hj (ε*(n:ℝ)^2) (by positivity)
  have hex : -2*(ε*(n:ℝ)^2)^2/((4*(d:ℝ)+3)^2*(n:ℝ)^2)=
      -(2*ε^2/(4*(d:ℝ)+3)^2)*(n:ℝ)^2 := by field_simp <;> ring
  change 1-(4:ℝ)^n*(2*Real.exp (-2*(ε*(n:ℝ)^2)^2/((4*(d:ℝ)+3)^2*(n:ℝ)^2)))≤_ at hh
  rw [hex] at hh
  have htail := hN n hn 2 (by norm_num)
  have heq : (4:ℝ)^n*(2*Real.exp (-(2*ε^2/(4*(d:ℝ)+3)^2)*(n:ℝ)^2))=
      2*(4:ℝ)^n*Real.exp (-(2*ε^2/(4*(d:ℝ)+3)^2)*(n:ℝ)^2) := by ring
  rw [heq] at hh
  have he : (2*ε^2/(4*(d:ℝ)+3)^2)/2=ε^2/(4*(d:ℝ)+3)^2 := by ring
  rw [he] at htail
  exact (sub_le_sub_left htail 1).trans hh

end Oberwolfach
