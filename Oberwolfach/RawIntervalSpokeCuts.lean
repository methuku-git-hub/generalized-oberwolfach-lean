module

public import Oberwolfach.RawIntervalSpokeDegrees
public import Oberwolfach.BipartiteQuadraticCut

@[expose] public section

/-! Large cuts of the actual ordinary spoke graph. The cut coefficient and
normalized size margin depend only on the lower spoke density. The order
threshold may depend on the interval length, as required by its local law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawIntervalSpokeMatrix_large_cuts
    (pstar ω : ℝ) (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V)
      (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ pH : ℝ,pstar≤pH → (∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ (X : Finset V) (Y : Finset U),
          1-pstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
          pstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
            (bipartiteMatrixCut (rawIntervalSpokeMatrix π d σ j) X Y:ℝ)) := by
  let ε : ℝ := pstar^2*ω/128
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨N₁,hN₁⟩ := rawIntervalSpokeMatrix_degree_event pstar ω hpstar hω d (q₀+1) hd
  obtain ⟨N₂,hN₂⟩ := rawIntervalCutCount_quadratic_event d hd ε hε (q₀+1)
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi π q hq hQ s hs hS j hnoshort pH hpH hj
  let n := Fintype.card V
  let m := Fintype.card U
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<m := (mul_pos hω hn0).trans_le hmlo
  have hm : 0<m := by exact_mod_cast hm0
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hdegree := hN₁ V U Γ Color (by omega) hmlo hmhi π q hq hQ s hs hS j hnoshort pH hpH hj
  have hcuts := hN₂ V U Γ Color (by omega) hm hmhi π q hq hQ s hs hS j hnoshort pH hj
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>(∀ v : V,pstar*(Fintype.card U:ℝ)/2≤((∑ u,rawIntervalSpokeMatrix π d σ j v u:ℕ):ℝ)) ∧
        (∀ u : U,pstar*(Fintype.card V:ℝ)/2≤((∑ v,rawIntervalSpokeMatrix π d σ j v u:ℕ):ℝ)))
    _ (1/(n:ℝ)^(q₀+1)) hcuts
  have hbase := (sub_le_sub_right hdegree (1/(n:ℝ)^(q₀+1))).trans hjoint
  have hsum := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤(1-1/(n:ℝ)^(q₀+1))-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsum 1 using 1 <;> ring
  apply (hbound.trans hbase).trans
  apply finiteLaw_probability_mono
  intro σ hσ X Y hlarge
  have hquad (S : Finset V) (T : Finset U) :
      |(bipartiteMatrixCut (rawIntervalSpokeMatrix π d σ j) S T:ℝ)-pH*S.card*T.card|≤
        (pstar^2/128)*(n:ℝ)*m := by
    unfold bipartiteMatrixCut
    rw [rawIntervalSpokeMatrix_cut]
    have hh := (hσ.2 S T).le
    have hscale := mul_le_mul_of_nonneg_left hmlo (by positivity : (0:ℝ)≤pstar^2/128*n)
    dsimp only [ε,n,m] at hh ⊢
    nlinarith only [hh,hscale]
  have hcross := mul_lt_mul_of_pos_right hlarge (mul_pos hn0 hm0)
  have heq : ((X.card:ℝ)/n+(Y.card:ℝ)/m)*((n:ℝ)*m)=
      (m:ℝ)*X.card+(n:ℝ)*Y.card := by field_simp <;> ring
  change (1-pstar/8)*((n:ℝ)*m)<((X.card:ℝ)/n+(Y.card:ℝ)/m)*((n:ℝ)*m) at hcross
  rw [heq] at hcross
  exact bipartiteMatrixCut_large_of_degree_and_quadratic (rawIntervalSpokeMatrix π d σ j)
    (rawIntervalSpokeMatrix_le_one π d σ j) hn hm pstar pH (pstar/16) (pstar^2/128)
    hpstar hpstar1 hpH le_rfl le_rfl hσ.1.1 hσ.1.2 hquad X Y
    (by convert hcross using 1 <;> ring)

end Oberwolfach
