module

public import Oberwolfach.TriangleRowCoversSamplingEvent
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

theorem triangle_row_cover_common_event (K κ p:ℝ) (hK:1≤K)
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
      (fun σ=>
    let R:=rawWheelGraph P σ\F
    let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
    ∀ (D E:SimpleGraph V) (L:ℝ),0≤L → L≤ρ*A.card →
      (∀ v,(F.degree v:ℝ)≤L) → (∀ v,(D.degree v:ℝ)≤L) → (∀ v,(E.degree v:ℝ)≤L) →
    ∀ (Z:Finset V),Z⊆A → ∀ (n:ℕ) (x:Fin n→V),
      (n:ℝ)≤θ*A.card → Function.Injective x → (∀ i,x i∈X) → (∀ i,x i∉Z) →
      (∀ i,(R\D).neighborFinset (x i)⊆Z) →
      (∀ i,|pR*(A∩P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η) →
      (∀ i,(R\D).degree (x i)=2*(H\E).degree (x i)) →
      ∃ M:Fin n→Finset (OrdinaryWheel (R\D) F (H\E).Adj 3),
        (∀ i,OrdinaryRowCover (M i) (x i) Z 0) ∧
        (∀ i j,i≠j → Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)) ∧
        (∀ i,∀ W∈M i,∀ k,x k∈(ordinaryWheelRim W).support ↔ k=i) ∧
        (∀ a∈Z,(ordinaryWheelRimGraph (Finset.univ.biUnion M)).degree a≤2*n) ∧
        (∀ a∈Z,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion M) a)).card≤n) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion M) a u)).card≤3*n) ) :=by
  obtain ⟨ε,η,θ,ρ,hε,hη,hθ,hρ,N₁,hcover⟩:=triangle_row_covers_on_sampling_event p κ hp hp1 hκ
  refine ⟨η,θ,ρ,hη,hθ,hρ,?_⟩
  intro d q₀ hd
  obtain ⟨N₂,hsample⟩:=triangle_sampling_with_parent_weights K κ p ε η hK hκ hp hε hη d q₀ hd
  refine ⟨max N₁ N₂,?_⟩
  intro V Γ Color _ _ _ _ P F π A B X Y hn hV hAY hXY hYB hBA hBA' hdeg hF hnoshort
    pR pH hpR hpR1 hpH hpH1 q hq hQ s hs hS j hj
  obtain ⟨weight,hw,hprob⟩:=hsample V Γ Color P A X (by omega) hV hdeg
  have hh:=hprob F π B hBA (fun x hx=>hYB.mono_left (Finset.insert_subset (hXY hx) hAY))
    hF hnoshort pR pH hpR hpR1 hpH q hq hQ s hs hS j hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  dsimp only
  intro D E L hL hLρ hFD hD hE Z hZA n x hnθ hx hxX hxZ hroot hbalance hbal
  obtain ⟨M,hM,hcross,_⟩:=hcover V Γ Color P F π d A B X Y (by omega) hAY hXY hYB hBA hBA' hdeg
    pR pH hpR hpR1 hpH hpH1 s j hj weight hw σ hσ.1 hσ.2
    D E L hL hLρ hFD hD hE Z hZA n x hnθ hx hxX hxZ hroot hbalance hbal
  obtain ⟨M',_hsub,hM',hcross',hroots,hbounds⟩:=rooted_ordinary_row_cover_family M x Z hx hxZ hM hcross
  refine ⟨M',hM',hcross',hroots,?_,?_,?_⟩
  · simpa only [Nat.zero_add,Nat.mul_one,Nat.mul_comm] using hbounds.1
  · simpa only [Nat.zero_add,Nat.mul_one] using hbounds.2.1
  · simpa only [Nat.mul_comm] using hbounds.2.2

end Oberwolfach
