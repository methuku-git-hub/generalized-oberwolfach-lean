module

public import Oberwolfach.TriangleComparisonCover
public import Oberwolfach.TriangleRowCoverParameters
public import Oberwolfach.EndpointFactorUnderDeletion
public import Oberwolfach.SequentialRowCover
public import Oberwolfach.RowCoverUnion

@[expose] public section

/-! Successive triangle row covers with the original parent matching
weights on the original domain A, with the new endpoints confined to X.
The set X may be chosen later; neither weights nor error scales change.
Every factor is obtained from the proved endpoint theorem after
an explicitly bounded comparison deletion. No factor-existence assumption
is left in the statement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_row_covers_from_fixed_weights (p κ c C : ℝ)
    (hp:0<p) (hp1:p≤1) (hκ:0<κ) (hc:0<c) (hC:0<C) :
    ∃ ε₀ τ η K θ:ℝ,0<ε₀ ∧ 0<τ ∧ 0<η ∧ 0<K ∧ 0<θ ∧ ∃ N:ℕ,
      ∀ (V:Type) [Fintype V] [DecidableEq V],
      ∀ (P Q H F:SimpleGraph V) (A B X:Finset V) (n:ℕ) (x:Fin n→V),
      N≤A.card → (n:ℝ)≤θ*A.card → Function.Injective x →
      Disjoint A B → X⊆A → (∀ i,x i∉X) → (∀ i,x i∉B) →
      (∀ i,Q.neighborFinset (x i)⊆X) → (∀ i,H.neighborFinset (x i)⊆B) →
      (∀ a∈X,H.neighborFinset a⊆B) → Q≤P\F → (∀ u∈B,∀ v,¬F.Adj u v) →
      ∀ q s ε L δ ξ:ℝ,p≤q → q≤1 → p≤s → s≤1 → ε≤ε₀/2 → 0≤L → 0≤δ →
      L≤τ*A.card → κ*A.card≤(B.card:ℝ) → B.card≤A.card →
      (∀ i,∀ v∈insert (x i) A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ i,∀ X J:Finset V,x i∈X → X⊆insert (x i) A → J⊆B →
        X.card≤3 → J.card≤2 → X.card+J.card≤4 →
        q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-ε*A.card≤
          ((common (common A X (fun v=>Q.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ)) →
      (∀ i,∀ X:Finset V,x i∈X → X⊆insert (x i) A → (X.card=1 ∨ X.card=3) →
        (∀ v∈X,∀ w∈X,¬F.Adj v w) →
        (s^X.card-ε)*B.card≤((common B X (fun v=>H.neighborFinset v)).card:ℝ)) →
      ∀ weight:Fin n→Sym2 V→ℝ,
      (∀ i,∀ v∈A∩P.neighborFinset (x i),∀ w∈A∩P.neighborFinset (x i),
        0≤weight i s(v,w) ∧ weight i s(v,w)≤C/A.card) →
      (∀ i,∀ v∈A∩P.neighborFinset (x i),∑ w∈A∩P.neighborFinset (x i),weight i s(v,w)=1) →
      (∀ i,∀ v∈A∩P.neighborFinset (x i),∀ w∈A∩P.neighborFinset (x i),
        ¬P.Adj v w → weight i s(v,w)=0) →
      (∀ i,∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset (x i)) (x i)).edgeSet,
        c/A.card≤weight i e ∧ weight i e≤C/A.card) →
      (∀ i,|q*(A∩P.neighborFinset (x i)).card/(2*B.card*s)-1|≤δ) →
      (∀ i,∀ v∈common A {x i} (fun y=>(P\F).neighborFinset y),
        |endpointRowPotential P Q H F A B (x i) v (weight i) (B.card*q^2*s^3)-
          endpointEligibleRowWeight F (A∩P.neighborFinset (x i)) (x i) v
            (fun v w=>weight i s(v,w))|≤ξ) →
      (∀ i,∀ u∈B,
        |endpointIndexPotential P Q H F A (x i) u (weight i) (B.card*q^2*s^3)-
          q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset (x i)) (x i)).edgeFinset,weight i e)|≤ξ) →
      δ+K*L/A.card+ξ≤η/2 → (∀ i,Q.degree (x i)=2*H.degree (x i)) →
      ∃ M:Fin n→Finset (OrdinaryWheel Q F H.Adj 3),
        (∀ i,OrdinaryRowCover (M i) (x i) X 0) ∧
        (∀ i j,i≠j → Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)) ∧
        (∀ a∈X,(ordinaryWheelRimGraph (Finset.univ.biUnion M)).degree a≤2*n) ∧
        (∀ a∈X,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion M) a)).card≤n) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion M) a u)).card≤3*n) := by
  obtain ⟨ε₀,τ,η,K,hε,hτ,hη,hK,N,hfactor⟩:=endpoint_factor_after_bounded_deletion p κ c C hp hp1 hκ hc hC
  have hCnorm:0<C/(κ*p^5):=by positivity
  obtain ⟨θ,hθ,hparameters⟩:=triangle_row_cover_parameters ε₀ η κ (C/(κ*p^5)) hε hη hκ hCnorm
  refine ⟨ε₀,τ,η,K,θ,hε,hτ,hη,hK,hθ,max N 1,?_⟩
  intro V _ _ P Q H F A B X n x hn hnθ hx hAB hXA hxA hxB hA hB hHA hQ hFB
    q s ε L δ ξ hq hq1 hs hs1 hε' hL hδ hLτ hBA hBA' hdeg hF hrows hindices
    weight hw hsum hzero hpos hbalance hrow hindex herr hbal
  have haN:0<A.card:=by omega
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr haN
  have hparams:=hparameters A.card B.card n ha hBA (Nat.cast_nonneg n) hnθ
  have hex:∃ M:Fin n→Finset (OrdinaryWheel Q F H.Adj 3),
      (∀ i,OrdinaryRowCover (M i) (x i) X 0) ∧
      (∀ i j,i≠j → Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)):=by
    apply sequential_ordinary_row_covers x hx X hxA
    intro i M havoid hMr hMs hMc
    let D:=spanningRestriction (ordinaryWheelRimGraph M) X
    let E:=bipartiteRelationGraph X B (hAB.mono_left hXA) (ordinaryPackingSpokes M)
    have hD (a:V):(D.degree a:ℝ)≤3*n:=spanningRestriction_degree_bound _ X (3*n) (by positivity)
      (fun a ha=>by have hh:=hMr a ha;norm_num at hh;exact_mod_cast (show (ordinaryWheelRimGraph M).degree a≤3*n from by omega)) a
    have hE (a:V):(E.degree a:ℝ)≤3*n:=bipartiteRelationGraph_degree_bound X B (hAB.mono_left hXA) _ (3*n) (by positivity)
      (fun a ha=>by have hh:=hMs a ha;norm_num at hh;exact_mod_cast (show (Finset.univ.filter (ordinaryPackingSpokes M a)).card≤3*n from by omega))
      (fun u _=>by have hh:=hMc u;exact_mod_cast (show (Finset.univ.filter (fun a=>ordinaryPackingSpokes M a u)).card≤3*n from by omega)) a
    have hxD (a:V):¬D.Adj (x i) a:=by intro h;exact hxA i ((spanningRestriction_adj _ X (x i) a).mp h).2.1
    have hxE (a:V):¬E.Adj (x i) a:=bipartiteRelationGraph_outside X B (hAB.mono_left hXA) _ (hxA i) (hxB i)
    have hS:common A {x i} (fun v=>(Q\D).neighborFinset v)=Q.neighborFinset (x i):=by
      ext a
      simp only [mem_common_iff,Finset.mem_singleton,forall_eq,SimpleGraph.mem_neighborFinset,
        SimpleGraph.sdiff_adj,hxD,not_false_eq_true,and_true]
      exact ⟨And.right,fun h=>⟨hXA (hA i ((Q.mem_neighborFinset (x i) a).mpr h)),h⟩⟩
    have hT:common B {x i} (fun v=>(H\E).neighborFinset v)=H.neighborFinset (x i):=by
      ext a
      simp only [mem_common_iff,Finset.mem_singleton,forall_eq,SimpleGraph.mem_neighborFinset,
        SimpleGraph.sdiff_adj,hxE,not_false_eq_true,and_true]
      exact ⟨And.right,fun h=>⟨hB i ((H.mem_neighborFinset (x i) a).mpr h),h⟩⟩
    have hfac:=hfactor V P Q H F D E A B (x i) ((le_max_left N 1).trans hn) hAB hQ hFB
      q s ε L (3*n) δ ξ hq hq1 hs hs1 (by linarith only [hε',hparams.1]) hL (by positivity) hδ
      hLτ hBA hBA' (hdeg i) hF hD hE (hrows i) (hindices i) (weight i)
      (hw i) (hsum i) (hzero i) (hpos i) (hbalance i) (hrow i) (hindex i)
      (by linarith only [herr,hparams.2])
      (by rw [hS,hT,SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree];exact hbal i)
    apply triangle_comparison_cover_of_factor Q H F A B X hAB hXA (x i) (hxA i) (hxB i) (hA i) (hB i)
      hHA (fun a ha=>(hQ ha).2) M havoid
    convert hfac using 1 <;> rw [hS,hT]
  obtain ⟨M,hM,hcross⟩:=hex
  have hbounds:=row_cover_union_degree_bounds M x X hxA hM
  refine ⟨M,hM,hcross,?_,?_,?_⟩
  · simpa only [Nat.zero_add,Nat.mul_one,Nat.mul_comm] using hbounds.1
  · simpa only [Nat.zero_add,Nat.mul_one] using hbounds.2.1
  · simpa only [Nat.mul_comm] using hbounds.2.2

end Oberwolfach
