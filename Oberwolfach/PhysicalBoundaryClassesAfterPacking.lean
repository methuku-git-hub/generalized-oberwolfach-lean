module

public import Oberwolfach.PhysicalMaskChangeIncidences
public import Oberwolfach.GreedyGraphCandidates
public import Oberwolfach.MarkedBoundaryEndpointSampling

@[expose] public section

/-! Exact later boundary classes are defined using the remaining physical
graph. Their difference from the reserved classes is bounded by the sum
of the actual leftover and covering degrees, on the same fixed domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {W A:Type} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

theorem physical_coin_single_incidence_card (coin:A↪Sym2 W) (D:SimpleGraph W) (S:Finset A) (x:W)
    (hS:∀ a∈S,coin a∈D.edgeSet∧x∈coin a):S.card≤D.degree x:=by
  have hsub:S.image coin⊆D.incidenceFinset x:=by
    intro e he
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
    exact SimpleGraph.mem_incidenceFinset.mpr (hS a ha)
  calc
    S.card=(S.image coin).card:=(Finset.card_image_of_injective S coin.injective).symm
    _≤(D.incidenceFinset x).card:=Finset.card_le_card hsub
    _=D.degree x:=by simp

theorem physical_boundary_class_after_packing (coin:A↪Sym2 W) (S:Finset A) (x:W)
    (G C D:SimpleGraph W) (σ:Sym2 W→Bool)
    (hG:∀ a∈S,coin a∈G.edgeSet∧x∈coin a)
    (hCR:Disjoint C (retainedGraph G σ)):
    (changed (S.filter (fun a=>σ (coin a)=true))
      (S.filter (fun a=>coin a∈((G\C)\D).edgeSet))).card≤
        ((G\retainedGraph G σ)\C).degree x+D.degree x:=by
  apply le_trans (b:=(((G\retainedGraph G σ)\C)⊔D).degree x)
  · rw [←SimpleGraph.ncard_neighborSet]
    have haux:=physical_coin_single_incidence_card coin (((G\retainedGraph G σ)\C)⊔D)
      (changed (S.filter (fun a=>σ (coin a)=true)) (S.filter (fun a=>coin a∈((G\C)\D).edgeSet))) x
    simp only [←SimpleGraph.ncard_neighborSet] at haux
    apply haux
    intro a ha
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter] at ha
    have hS:a∈S:=by tauto
    have hc:σ (coin a)≠decide (coin a∈((G\C)\D).edgeSet):=by
      intro he
      have hh:(σ (coin a)=true)↔coin a∈((G\C)\D).edgeSet:=by simp only [he,decide_eq_true_eq]
      simp only [hh] at ha
      tauto
    exact ⟨boundary_after_packing_changed_coin G C D σ hCR (coin a) (hG a hS).1 hc,(hG a hS).2⟩
  · simpa only [←SimpleGraph.ncard_neighborSet] using graph_degree_sup_le ((G\retainedGraph G σ)\C) D x

variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem marked_endpoint_class_after_packing (π:Equiv.Perm V) (mark incoming:Bool) (x:V)
    (L:Finset V) (G C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hG:∀ v∈L,markedBoundaryEndpointCoin (U:=U) π mark incoming x (Sum.inl v)∈G.edgeSet)
    (hCR:Disjoint C (retainedGraph G σ)):
    (changed (L.filter (fun v=>σ (markedBoundaryEndpointCoin π mark incoming x (Sum.inl v))=true))
      (L.filter (fun v=>markedBoundaryEndpointCoin π mark incoming x (Sum.inl v)∈((G\C)\D).edgeSet))).card≤
        ((G\retainedGraph G σ)\C).degree (Sum.inl (if mark&&incoming then π x else x))+
          D.degree (Sum.inl (if mark&&incoming then π x else x)):=by
  let coin:V↪Sym2 (V⊕U):=(Function.Embedding.inl).trans (markedBoundaryEndpointCoin π mark incoming x)
  apply physical_boundary_class_after_packing coin L _ G C D σ _ hCR
  intro v hv
  refine ⟨hG v hv,?_⟩
  change Sum.inl (if mark&&incoming then π x else x)∈markedBoundaryEndpointCoin π mark incoming x (Sum.inl v)
  rw [marked_boundary_endpoint_rim_coin]
  cases mark <;> cases incoming <;> simp

theorem marked_spoke_class_after_packing (x:V) (B:Finset U)
    (G C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hG:∀ u∈B,s(Sum.inl x,Sum.inr u)∈G.edgeSet)
    (hCR:Disjoint C (retainedGraph G σ)):
    (changed (B.filter (fun u=>σ s(Sum.inl x,Sum.inr u)=true))
      (B.filter (fun u=>((G\C)\D).Adj (Sum.inl x) (Sum.inr u)))).card≤
      ((G\retainedGraph G σ)\C).degree (Sum.inl x)+D.degree (Sum.inl x):=by
  let coin:U↪Sym2 (V⊕U):=(Function.Embedding.inr).trans (markedBoundaryEndpointCoin (Equiv.refl V) false false x)
  apply physical_boundary_class_after_packing coin B _ G C D σ _ hCR
  intro u hu
  exact ⟨hG u hu,by change Sum.inl x∈s(Sum.inl x,Sum.inr u);simp⟩

theorem marked_spoke_column_after_packing (u:U) (A:Finset V)
    (G C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hG:∀ x∈A,s(Sum.inl x,Sum.inr u)∈G.edgeSet)
    (hCR:Disjoint C (retainedGraph G σ)):
    (changed (A.filter (fun x=>σ s(Sum.inl x,Sum.inr u)=true))
      (A.filter (fun x=>((G\C)\D).Adj (Sum.inl x) (Sum.inr u)))).card≤
      ((G\retainedGraph G σ)\C).degree (Sum.inr u)+D.degree (Sum.inr u):=by
  let coin:V↪Sym2 (V⊕U):=⟨fun x=>s(Sum.inl x,Sum.inr u),by
    intro x y he
    rcases Sym2.eq_iff.mp he with ⟨h,_⟩|⟨h,_⟩
    · exact Sum.inl.inj h
    · exact (Sum.inl_ne_inr h).elim⟩
  apply physical_boundary_class_after_packing coin A _ G C D σ _ hCR
  intro x hx
  exact ⟨hG x hx,by change Sum.inr u∈s(Sum.inl x,Sum.inr u);simp⟩

end Oberwolfach
