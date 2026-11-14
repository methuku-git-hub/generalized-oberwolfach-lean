module

public import Oberwolfach.TwoDomainRowCoverEvent
public import Oberwolfach.HubToRowDeletion

@[expose] public section

/-! The original row event remains valid after every permissible earlier
hub cover. The proof preserves the root stars, charges the actual rim-degree
loss, and proves physical disjointness from the already chosen wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_row_cover_event_after_hubs (r:ℕ) (hr:4≤r) (C₀ α ω p₀:ℝ)
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
        ∀ (nh:ℕ) (u:Fin nh→U),Function.Injective u →
        ∀ (T:Fin nh→Finset V) (M:Finset (OrdinaryWheel Q F H r)),
        (∀ i,T i⊆X) → (∀ i,u i∉B) → (2*nh:ℝ)≤L →
        (∀ v,(ordinaryWheelRimGraph M).degree v≤2*nh) →
        M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
          Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i))) →
        ∃ C:Fin n→Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
          (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) r),
          (∀ i,OrdinaryRowCover (C i) (x i) X K) ∧
          (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
          (∀ i,∀ W∈C i,∀ k,x k∈(ordinaryWheelRim W).support ↔ k=i) ∧
          (∀ a∈X,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤n*(2*(K+1))) ∧
          (∀ a∈X,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤n*(K+1)) ∧
          (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion C) a u)).card≤n*r) ∧
          (∀ i,Disjoint ((C i).biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources))):=by
  obtain ⟨K,hK,θ,ε₀,hθ,hε₀,hcover⟩:=ordinary_two_domain_row_cover_event r hr C₀ α ω p₀ hC₀ hα hω hp₀ hp₀1
  refine ⟨K,hK,θ,ε₀/2,hθ,by positivity,?_⟩
  intro d D q₀ hd
  obtain ⟨N,hN⟩:=hcover d D q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A B hn hV hU hωU hF hD hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 hpH1 q hq hQ s hs hS j hj
  have hh:=hN V U Γ Color P F π A B hn hV hU hωU hF hD hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 hpH1 q hq hQ s hs hS j hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Q H L hL hLa hLb hQP hchangeQ hchangeHr hchangeHc X hXA hmissing
    n x hnθ hx hxX hroot hFx hbal hrootB nh u hu T M hTX hnotB hnh hMdeg hunion
  let R:=Q\ordinaryWheelRimGraph M
  let H':V→U→Prop:=fun v a=>H v a∧¬ordinaryPackingSpokes M v a
  have hinterfaces:=ordinary_hub_deletion_fixed_domain M u T A B hnotB hunion hMdeg
  have hstars (i:Fin n):
      R.neighborFinset (x i)=Q.neighborFinset (x i) ∧
      Finset.univ.filter (H' (x i))=Finset.univ.filter (H (x i)):=
    ordinary_hub_deletion_preserves_row_balance M (by omega) u hu T X hTX hunion (x i) (hxX i)
  have hnewQ (v:V):((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩R.neighborFinset v)).card:ℝ)≤2*L:=by
    have htri:((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩R.neighborFinset v)).card:ℝ)≤
        (changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v)).card+
        (changed (A∩Q.neighborFinset v) (A∩R.neighborFinset v)).card:=by
      exact_mod_cast changed_card_triangle (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v) (A∩R.neighborFinset v)
    have hdel:((changed (A∩Q.neighborFinset v) (A∩R.neighborFinset v)).card:ℝ)≤2*nh:=by
      exact_mod_cast hinterfaces.1 v
    linarith only [htri,hdel,hchangeQ v,hnh]
  have hnewHr (v:V):((changed (B∩Finset.univ.filter (rawWheelSpokes π d σ j v))
      (B∩Finset.univ.filter (H' v))).card:ℝ)≤2*L:=by
    rw [hinterfaces.2.1 v]
    linarith only [hchangeHr v,hL]
  have hnewHc (a:U) (ha:a∈B):((changed (A∩Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v a))
      (A∩Finset.univ.filter (fun v=>H' v a))).card:ℝ)≤2*L:=by
    rw [hinterfaces.2.2 a ha]
    linarith only [hchangeHc a ha,hL]
  obtain ⟨C,hC,hcross,hroots,hdegrees⟩:=hσ R H' (2*L) (by positivity)
    (by nlinarith only [hLa]) (by nlinarith only [hLb]) (sdiff_le.trans hQP)
    (fun v=>by convert hnewQ v using 1 <;> congr!) (fun v=>by convert hnewHr v using 1 <;> congr!)
    (fun a ha=>by convert hnewHc a ha using 1 <;> congr!) X hXA hmissing n x hnθ hx hxX
    (fun i=>by
      have he:R.neighborFinset (x i)=Q.neighborFinset (x i):=by
        convert (hstars i).1 using 1 <;> congr!
      convert he ▸ hroot i using 1 <;> congr!)
    (fun i a ha=>hFx i a ha.1)
    (fun i=>by
      have hdegR:R.degree (x i)=Q.degree (x i):=by
        rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree,(hstars i).1]
      have he:=congrArg (fun S:Finset U=>2*S.card) (hstars i).2
      convert hdegR.trans ((hbal i).trans he.symm) using 1 <;> congr!)
    (fun i a ha=>hrootB i a ha.1)
  refine ⟨C,hC,hcross,hroots,hdegrees.1,hdegrees.2.1,hdegrees.2.2,?_⟩
  intro i
  apply Finset.disjoint_left.mpr
  intro e he heM
  obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
  exact Finset.disjoint_left.mp (ordinary_wheel_avoids_removed_packing M W) heW heM

end Oberwolfach
