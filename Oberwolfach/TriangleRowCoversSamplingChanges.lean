module

public import Oberwolfach.TriangleRowCoversFromWeights
public import Oberwolfach.TriangleSamplingMargins
public import Oberwolfach.RawTriangleGraphCounts
public import Oberwolfach.TriangleCountsAfterChanges
public import Oberwolfach.EndpointPotentialAdaptiveChanges
public import Oberwolfach.OrdinaryConflictWheelTransport

@[expose] public section

/-! Actual successive triangle row covers on the proved original-law
sampling event. All later deletions, free sets and balanced root lists are
chosen after that event, with the original parent weights retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 512
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_row_covers_on_sampling_event_with_changes (p κ:ℝ) (hp:0<p) (hp1:p≤1) (hκ:0<κ):
    ∃ ε η θ ρ:ℝ,0<ε ∧ 0<η ∧ 0<θ ∧ 0<ρ ∧ ∃ N:ℕ,
    ∀ (V Γ Color:Type) [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A B X Y:Finset V),
      N≤A.card → A⊆Y → X⊆Y → ∀ hYB:Disjoint Y B,κ*A.card≤(B.card:ℝ) → B.card≤A.card →
      (∀ x∈X,∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
    ∀ (pR pH:ℝ),p≤pR → pR≤1 → p≤pH → pH≤1 →
    ∀ (s:V→Color→ℝ) (j:Color),(∀ u,s u j=pH) →
    ∀ (weight:V→Sym2 V→ℝ),
      (∀ x∈X,
        (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
          0≤weight x s(v,w)∧weight x s(v,w)≤40/A.card) ∧
        (∀ v∈A∩P.neighborFinset x,∑ w∈A∩P.neighborFinset x,weight x s(v,w)=1) ∧
        (∀ v w,¬P.Adj v w→weight x s(v,w)=0) ∧
        (∀ F':SimpleGraph V,∀ e∈(endpointEligibleGraph P F' (A∩P.neighborFinset x) x).edgeSet,
          (1/30:ℝ)/A.card≤weight x e∧weight x e≤40/A.card)) →
    ∀ (σ:RawWheelOutcome V V Γ Color),
      (RawOrdinaryRows P π d 3 A pR s j (ε*A.card) σ ∧
        RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ) →
      EndpointPotentialEstimates P F π d A B X pR pH j weight η σ →
    let R:=rawWheelGraph P σ\F
    let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
    ∀ (Q J:SimpleGraph V) (L:ℝ),0≤L → L≤ρ*A.card → Q≤P\F →
      (∀v,(F.degree v:ℝ)≤L) →
      (∀v,((changed (A∩R.neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L) →
      (∀v,((changed (B∩H.neighborFinset v) (B∩J.neighborFinset v)).card:ℝ)≤L) →
      (∀u∈B,((changed (A∩H.neighborFinset u) (A∩J.neighborFinset u)).card:ℝ)≤L) →
      (∀v,((R\Q).degree v:ℝ)≤L) → (∀v,((Q\R).degree v:ℝ)≤L) →
      (∀v,((H\J).degree v:ℝ)≤L) → (∀v,((J\H).degree v:ℝ)≤L) →
      (∀a∈Y,J.neighborFinset a⊆B) →
    ∀ (Z:Finset V),Z⊆A → ∀ (n:ℕ) (x:Fin n→V),
      (n:ℝ)≤θ*A.card → Function.Injective x → (∀ i,x i∈X) → (∀ i,x i∉Z) →
      (∀ i,Q.neighborFinset (x i)⊆Z) →
      (∀ i,|pR*(A∩P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η) →
      (∀ i,Q.degree (x i)=2*J.degree (x i)) →
      ∃ M:Fin n→Finset (OrdinaryWheel Q F J.Adj 3),
        (∀ i,OrdinaryRowCover (M i) (x i) Z 0) ∧
        (∀ i j,i≠j → Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)) ∧
        (∀ a∈Z,(ordinaryWheelRimGraph (Finset.univ.biUnion M)).degree a≤2*n) ∧
        (∀ a∈Z,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion M) a)).card≤n) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion M) a u)).card≤3*n):=by
  obtain ⟨ε₀,τ,η,K,θ,hε,hτ,hη,hK,hθ,N,hcover⟩:=triangle_row_covers_from_fixed_weights p κ (1/30) 40 hp hp1 hκ (by norm_num) (by norm_num)
  let C:ℝ:=40/(κ*p^5)
  have hC:0<C:=by dsimp [C];positivity
  obtain ⟨ρ,hρ,hmargins⟩:=triangle_sampling_margins ε₀ τ η K C κ hε hτ hη hK hC hκ
  refine ⟨ε₀/4,η/8,θ,ρ/2,by positivity,by positivity,hθ,by positivity,max N 1,?_⟩
  intro V Γ Color _ _ _ _ P F π d A B X Y hn hAY hXY hYB hBA hBA' hdeg
    pR pH hpR hpR1 hpH hpH1 s j hj weight hw σ hcounts hpot
  dsimp only
  intro Q J L hL hLρ hQP hF hQchg hHr hHc hRQ hQR hHJ hJH hJdom Z hZA n x hnθ hx hxX hxZ hroot hbalance hbal
  let F₀:=spanningRestriction F Y
  let R:=rawWheelGraph P σ\F
  let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
  have ha:0<A.card:=by omega
  have ha0:(0:ℝ)<A.card:=Nat.cast_pos.mpr ha
  have hm:=hmargins A.card B.card (2*L) ha0 hBA (by positivity) (by nlinarith)
  have hraw:=raw_triangle_counts_on_spoke_domain P F π d A B Y hAY hYB pR pH (ε₀/4) s j hj σ hcounts.1 hcounts.2
  have hc:=triangle_relative_counts_after_changes P (rawWheelGraph P σ) H F Q J A B Y hAY
    pR pH (ε₀/4) (ε₀/2) L (hp.le.trans hpR) (hp.le.trans hpH) hL (by nlinarith [hm.2.1]) (by nlinarith [hm.2.2.1]) hF hQchg hHr hHc hraw.1 hraw.2
  have hwedge (z:V) (hz:z∈X) (e:Sym2 V) (he:e∈(endpointEligibleGraph P F (A∩P.neighborFinset z) z).edgeSet):
      0≤weight z e∧weight z e≤40/A.card:=by
    induction e using Sym2.ind with
    | _ a b=>exact (hw z hz).1 a he.1 b he.2.1
  have hpot':=endpoint_potential_estimates_after_changes P F π d A B X Y ha hBA' hAY hXY hYB
    p pR pH κ 40 (η/8) hp hpR hpH hκ (by norm_num) hBA j weight hwedge σ hpot Q J L hL hRQ hQR hHJ hJH
  have hB (a:V) (haY:a∈Y):J.neighborFinset a⊆B:=hJdom a haY
  have hQ:Q≤P\F₀:=by
    intro a b hab
    refine ⟨(hQP hab).1,?_⟩
    exact fun hf=>(hQP hab).2 (spanningRestriction_le F Y hf)
  have hF₀ (a:V):(F₀.degree a:ℝ)≤L:=
    (Nat.cast_le.mpr (SimpleGraph.degree_le_of_le (spanningRestriction_le F Y))).trans (hF a)
  obtain ⟨M,hM,hcross,_hbounds⟩:=hcover V P Q J F₀ A B Z n x (by omega) hnθ hx (hYB.mono_left hAY)
    hZA hxZ (fun i hi=>Finset.disjoint_left.mp hYB (hXY (hxX i)) hi) (by convert hroot using 1 <;> congr!)
    (fun i=>by convert hB (x i) (hXY (hxX i)) using 1 <;> congr!) (fun a ha=>by convert hB a (hAY (hZA ha)) using 1 <;> congr!) hQ
    (restricted_conflict_has_no_hub_edges F Y B hYB)
    pR pH (ε₀/2) (2*L) (η/8) (η/8+10*C*L/A.card) hpR hpR1 hpH hpH1 le_rfl (by positivity) (by positivity)
    hm.1 hBA hBA' (fun i=>hdeg (x i) (hxX i)) (fun a=>by have hh:=hF₀ a; linarith)
    (fun i S J _hxS hS hJ hSc hJc htot=>
      by convert hc.1 S J (hS.trans (Finset.insert_subset (hXY (hxX i)) hAY)) hJ hSc hJc htot using 1 <;> congr!)
    (fun i S _hxS hS hSc hI=>
      by convert hc.2 S (hS.trans (Finset.insert_subset (hXY (hxX i)) hAY)) (by omega) hI using 1 <;> congr!)
    (fun i=>weight (x i))
    (fun i=>(hw (x i) (hxX i)).1)
    (fun i=>(hw (x i) (hxX i)).2.1)
    (fun i v _ w _=>(hw (x i) (hxX i)).2.2.1 v w)
    (fun i=>(hw (x i) (hxX i)).2.2.2 F₀)
    hbalance (fun i=>(hpot' (x i) (hxX i)).1)
    (fun i u hu=>((hpot' (x i) (hxX i)).2 u hu).trans (by dsimp [C];gcongr;norm_num))
    (by convert hm.2.2.2 using 1 <;> ring) (by convert hbal using 1 <;> congr!)
  convert ordinary_row_covers_full_conflict Y Z (hZA.trans hAY) n x
    (fun i=>hXY (hxX i)) hxZ M hM hcross using 1 <;> congr!

end Oberwolfach
