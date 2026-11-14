module

public import Oberwolfach.OrdinaryDomainNeighbourhoodEvent
public import Oberwolfach.TwoFixedDomainRowCovers
public import Oberwolfach.RootedRowCover

@[expose] public section

/-! A single event under the original raw law supplies successive row
covers for every subsequent bounded modification and free vertex set.
Both counting domains A and B are fixed before sampling; only neighbourhood
changes inside the relevant domain are charged to the error budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_two_domain_row_cover_event (r:ℕ) (hr:4≤r) (C₀ α ω p₀:ℝ)
    (hC₀:1≤C₀) (hα:0<α) (hω:0<ω) (hp₀:0<p₀) (hp₀1:p₀≤1):
    ∃ K:ℕ,0<K ∧ ∃ θ ε₀:ℝ,0<θ ∧ 0<ε₀ ∧ ∀ d D q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (B:Finset U),N≤A.card →
      (Fintype.card V:ℝ)≤C₀*A.card → (Fintype.card U:ℝ)≤C₀*A.card → ω*A.card≤(B.card:ℝ) →
      permutationConflictGraph π (3*d)≤F → (∀ a,F.degree a≤D) →
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
        6*L≤ε₀*A.card → 6*L≤ε₀*B.card → Q≤P →
        (∀ v,((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L) →
        (∀ v,((changed (B∩Finset.univ.filter (rawWheelSpokes π d σ j v)) (B∩Finset.univ.filter (H v))).card:ℝ)≤L) →
        (∀ u∈B,((changed (A∩Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
          (A∩Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L) →
        ∀ (X:Finset V),X⊆A → ((A\X).card:ℝ)≤p₀^6*(min α 1)*A.card/8 →
        ∀ (n:ℕ) (x:Fin n→V),(n:ℝ)≤θ*A.card → Function.Injective x → (∀ i,x i∉X) →
        (∀ i,Q.neighborFinset (x i)⊆X) →
        (∀ i a,Q.Adj (x i) a → ¬F.Adj (x i) a) →
        (∀ i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card) →
        (∀ i u,H (x i) u → u∈B) →
        ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
          (∀ i,OrdinaryRowCover (C i) (x i) X K) ∧
          (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
          (∀ i,∀ W∈C i,∀ k,x k∈(ordinaryWheelRim W).support ↔ k=i) ∧
          (∀ a∈X,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤n*(2*(K+1))) ∧
          (∀ a∈X,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤n*(K+1)) ∧
          (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion C) a u)).card≤n*r)):=by
  obtain ⟨K,hK,θ,ε₀,hθ,hε₀,hcover⟩:=ordinary_two_fixed_domain_row_covers
    r hr C₀ α ω p₀ (le_trans (by norm_num) hC₀) hα hω hp₀ hp₀1
  refine ⟨K,hK,θ,ε₀,hθ,hε₀,?_⟩
  intro d D q₀ hd
  obtain ⟨N₁,hN₁⟩:=hcover D
  obtain ⟨N₂,hN₂⟩:=ordinary_two_domain_neighbourhood_common_event C₀ ω (ε₀/2) hC₀ hω (by positivity) d q₀ hd
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A B hn hV hU hωU hF hD hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 hpH1 q hq hQ s hs hS j hj
  have hh:=hN₂ V U Γ Color P F π A B (by omega) hV hU hωU hF hnoshort
    pR hpR hpR1 q hq hQ s hs hS j pH hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Q H L hL hLa hLb hQP hchangeQ hchangeHr hchangeHc X hXA hmissing n x hnθ hx hxA hSA hFx hbal hrootB
  have hcounts:=ordinary_two_domain_counts_under_changes P (rawWheelGraph P σ) Q F
    (rawWheelSpokes π d σ j) H A B pR pH (ε₀/2) ε₀ L hL
    (by linarith only [hLa]) (by linarith only [hLb]) hchangeQ hchangeHr hchangeHc
    (by
      intro S J _hJB hSc hJc
      have ht:=(hσ.1 S J hSc (by omega)).le
      simpa only [hj,Finset.prod_const] using ht)
    (fun S hSc hI=>(hσ.2 S hSc hI).le)
  obtain ⟨M,hM,hcross,_⟩:=hN₁ V U P Q F H n x A X B pR pH ε₀ (by omega) hnθ hωU
    ((Nat.cast_le.mpr (Finset.card_le_univ B)).trans hU) hpR0 hpH0 hpH1 hε₀.le le_rfl
    hx hXA hxA hQP hmissing hSA hbal hrootB hD hFx hdeg hcounts.1 hcounts.2
  obtain ⟨M',_hsub,hM',hcross',hroots,hbounds⟩:=rooted_ordinary_row_cover_family M x X hx hxA hM hcross
  exact ⟨M',hM',hcross',hroots,hbounds⟩

end Oberwolfach
