module

public import Oberwolfach.TriangleRowCoverChangesNamed
public import Oberwolfach.TriangleSamplingWithParentWeights
public import Oberwolfach.RootedRowCover

@[expose] public section

/-! One event under the original law gives physical triangle row covers
for all later bounded deletions, free sets and balanced root lists.
The parent matching weights are constructed before the sample and used
unchanged in the proof; they are not hypotheses of this result. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 512
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_row_cover_changes_named_high_probability (K κ p:ℝ) (hK:1≤K)
    (hκ:0<κ) (hp:0<p) (hp1:p≤1):
    ∃ η θ ρ:ℝ,0<η ∧ 0<θ ∧ 0<ρ ∧ ∀ d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V Γ Color:Type) [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A B X Y:Finset V),
      N≤A.card → (Fintype.card V:ℝ)≤K*A.card → A⊆Y → X⊆Y →
    ∀ hYB:Disjoint Y B,κ*A.card≤(B.card:ℝ) → B.card≤A.card →
      (∀ x∈X,∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
    ∀ (q:V→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:V→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (TriangleRowCoverChangesEvent P F π d A B X Y hYB pR pH η θ ρ j) :=by
  obtain ⟨η,θ,ρ,hη,hθ,hρ,h⟩:=triangle_row_cover_changes_common_event K κ p hK hκ hp hp1
  refine ⟨η,θ,ρ,hη,hθ,hρ,?_⟩
  intro d q₀ hd
  obtain ⟨N,hN⟩:=h d q₀ hd
  refine ⟨N,?_⟩
  intro V Γ Color _ _ _ _ P F π A B X Y hn hV hAY hXY hYB hBA hBA' hdeg hF hnoshort
    pR pH hpR hpR1 hpH hpH1 q hq hQ s hs hS j hj
  have hh:=hN V Γ Color P F π A B X Y hn hV hAY hXY hYB hBA hBA' hdeg hF hnoshort
    pR pH hpR hpR1 hpH hpH1 q hq hQ s hs hS j hj
  convert hh using 1 <;> simp only [TriangleRowCoverChangesEvent] <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
