module

public import Oberwolfach.OrdinaryNeighbourhoodCommonEvent
public import Oberwolfach.OrdinaryRelativeCountChanges
public import Oberwolfach.OrdinaryRowCoverFromRelativeCounts

@[expose] public section

/-! On one original-law event, every later bounded modification with
balanced row roots admits the successive ordinary row covers. The outside
domain is fixed before exposure; the modified graphs and root list are not. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_row_cover_event (r:ℕ) (hr:4≤r) (C₀ α ω p₀:ℝ)
    (hC₀:1≤C₀) (hα:0<α) (hω:0<ω) (hp₀:0<p₀) (hp₀1:p₀≤1):
    ∃ K:ℕ,0<K ∧ ∃ θ ε₀:ℝ,0<θ ∧ 0<ε₀ ∧ ∀ d D q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V),N≤A.card →
      (Fintype.card V:ℝ)≤C₀*A.card → (Fintype.card U:ℝ)≤C₀*A.card → ω*A.card≤(Fintype.card U:ℝ) →
      permutationConflictGraph π (3*d)≤F → (∀ a,F.degree a≤D) →
      (∀ a b,P.Adj a b → ¬F.Adj a b) →
      (∀ a,(1/2+α)*A.card≤((A∩P.neighborFinset a).card:ℝ)) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1),p₀≤pR → p₀≤pH → pH≤1 →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (Q:SimpleGraph V) (H:V→U→Prop) (L:ℝ),0≤L →
        6*L≤ε₀*A.card → 6*L≤ε₀*Fintype.card U → Q≤P →
        (∀ v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
        (∀ v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
        (∀ u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
          (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L) →
        ∀ (n:ℕ) (x:Fin n→V),(n:ℝ)≤θ*A.card → Function.Injective x → (∀ i,x i∉A) →
        (∀ i,Q.neighborFinset (x i)⊆A) →
        (∀ i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card) →
        ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
          (∀ i,OrdinaryRowCover (C i) (x i) A K) ∧
          (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
          (∀ a∈A,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤n*(2*(K+1))) ∧
          (∀ a∈A,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤n*(K+1)) ∧
          (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion C) a u)).card≤n*r)):=by
  obtain ⟨K,hK,θ,ε₀,hθ,hε₀,hcover⟩:=ordinary_small_set_row_covers_from_relative_counts
    r hr C₀ α ω p₀ (le_trans (by norm_num) hC₀) hα hω hp₀ hp₀1
  refine ⟨K,hK,θ,ε₀,hθ,hε₀,?_⟩
  intro d D q₀ hd
  obtain ⟨N₁,hN₁⟩:=hcover D
  obtain ⟨N₂,hN₂⟩:=ordinary_neighbourhood_common_event C₀ ω (ε₀/2) hC₀ hω (by positivity) d q₀ hd
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A hn hV hU hωU hF hD hPF hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 hpH1 q hq hQ s hs hS j hj
  have hh:=hN₂ V U Γ Color P F π A (by omega) hV hU hωU hF hnoshort
    pR hpR hpR1 q hq hQ s hs hS j pH hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Q H L hL hLa hLb hQP hchangeQ hchangeHr hchangeHc n x hnθ hx hxA hSA hbal
  have hcounts:=ordinary_relative_counts_under_changes P (rawWheelGraph P σ) Q F
    (rawWheelSpokes π d σ j) H A pR pH (ε₀/2) ε₀ L hL
    (by linarith only [hLa]) (by linarith only [hLb]) hchangeQ hchangeHr hchangeHc
    (by
      intro S J hSc hJc
      have ht:=(hσ.1 S J hSc (by omega)).le
      simpa only [hj,Finset.prod_const] using ht)
    (fun S hSc hI=>(hσ.2 S hSc hI).le)
  exact hN₁ V U P Q F H n x A pR pH ε₀ (by omega) hnθ hωU hU hpR0 hpH0 hpH1 hε₀.le le_rfl
    hx hxA hQP hSA hbal hD (fun i a ha=>hPF (x i) a (hQP ha)) hdeg hcounts.1 hcounts.2

end Oberwolfach
