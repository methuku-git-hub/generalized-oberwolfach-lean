module

public import Oberwolfach.OrdinaryReferenceCuts
public import Oberwolfach.PermutationConflictDegree

@[expose] public section

/-! The ordinary completion cut lemma with its actual permutation conflict
graph. There is no caller-supplied conflict-degree assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_completion_large_cuts
    (α pstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hpstar : 0<pstar) (hω : 0<ω) :
    ∃ δ h : ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧
    ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (π : Equiv.Perm V),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ (pR pH : ℝ) (hR : 0≤pR) (hR1 : pR≤1),pstar≤pR → pstar≤pH →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
    let μ := (FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hR) (fun _=>hR1)
      d hd q hq hQ s hs hS)).prod (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin))
    1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun z=>
      (∀ (X : Finset V) (Y : Finset U),
        1-2*δ<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
        2*h*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
          (bipartiteMatrixCut (fun v u=>if rawWheelSpokes π d z.1 j v u then 1 else 0) X Y:ℝ)) ∧
      (∀ S T : Finset V,
        1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card V →
        2*h*min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
          (matrixCut (sampledOrientation ((rawWheelGraph P z.1)\permutationConflictGraph π (3*d)) z.2) S T:ℝ))) := by
  obtain ⟨δ,h,hδ,hδ1,hh,hmain⟩ := ordinary_reference_large_cuts α (min pstar 1) ω hα hα1
    (lt_min hpstar (by norm_num)) (min_le_right _ _) hω
  refine ⟨δ,h,hδ,hδ1,hh,?_⟩
  intro d q₀ hd
  obtain ⟨N,hN⟩ := hmain ((6*d:ℕ):ℝ) (by positivity) d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hmlo hmhi P hP π hnoshort pR pH hR hR1 hRlo hHlo
    q hq hQ s hs hS j hj
  have hF (v : V) : ((permutationConflictGraph π (3*d)).degree v:ℝ)≤((6*d:ℕ):ℝ) := by
    have hb := permutationConflictGraph_degree_le π (3*d) v
    have hb' : (permutationConflictGraph π (3*d)).degree v≤6*d := by omega
    exact_mod_cast hb'
  exact hN V U Γ Color hn hmlo hmhi P (permutationConflictGraph π (3*d)) hP
    (by intro v;simpa only [← SimpleGraph.ncard_neighborSet,← Nat.card_eq_fintype_card] using hF v)
    π hnoshort pR pH hR hR1 ((min_le_left _ _).trans hRlo) ((min_le_left _ _).trans hHlo)
    q hq hQ s hs hS j hj

end Oberwolfach
