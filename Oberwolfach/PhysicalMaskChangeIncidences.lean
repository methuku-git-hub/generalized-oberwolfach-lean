module

public import Oberwolfach.BoundaryAfterPacking
public import Oberwolfach.MarkedBoundaryPhysicalCoordinates

@[expose] public section

/-! Realized boundary changes after packing are charged to actual edges
left outside the reservation or used by the subsequent covering. The
auxiliary marked head is charged at its image under the permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {W A:Type} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

theorem physical_coin_incidence_card (coin:A↪Sym2 W) (D:SimpleGraph W) (S:Finset A) (x y:W)
    (hS:∀ a∈S,coin a∈D.edgeSet∧(x∈coin a∨y∈coin a)):
    S.card≤D.degree x+D.degree y:=by
  have hsub:S.image coin⊆D.incidenceFinset x∪D.incidenceFinset y:=by
    intro e he
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨hD,hxy⟩:=hS a ha
    rcases hxy with hx|hy
    · exact Finset.mem_union_left _ (SimpleGraph.mem_incidenceFinset.mpr ⟨hD,hx⟩)
    · exact Finset.mem_union_right _ (SimpleGraph.mem_incidenceFinset.mpr ⟨hD,hy⟩)
  calc
    S.card=(S.image coin).card:=(Finset.card_image_of_injective S coin.injective).symm
    _≤(D.incidenceFinset x∪D.incidenceFinset y).card:=Finset.card_le_card hsub
    _≤(D.incidenceFinset x).card+(D.incidenceFinset y).card:=Finset.card_union_le _ _
    _=D.degree x+D.degree y:=by simp

theorem boundary_after_packing_changed_coin (G C D:SimpleGraph W) (σ:Sym2 W→Bool)
    (hCR:Disjoint C (retainedGraph G σ)) (e:Sym2 W) (he:e∈G.edgeSet)
    (hc:σ e≠decide (e∈((G\C)\D).edgeSet)):
    e∈(((G\retainedGraph G σ)\C)⊔D).edgeSet:=by
  induction e using Sym2.ind with
  | _ x y=>
    have hG:G.Adj x y:=he
    have hdis:¬(C.Adj x y∧(retainedGraph G σ).Adj x y):=by
      rintro ⟨hC,hR⟩
      exact disjoint_graphs_no_common_edge C (retainedGraph G σ) hCR x y hC hR
    change (((G\retainedGraph G σ)\C)⊔D).Adj x y
    change σ s(x,y)≠decide (((G\C)\D).Adj x y) at hc
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj,retainedGraph] at hc hdis ⊢
    cases hs:σ s(x,y) <;> simp only [hs,Bool.false_eq_true,Bool.true_eq_false] at hc hdis ⊢
    · have hrem:(G.Adj x y∧¬C.Adj x y)∧¬D.Adj x y:=by
        by_contra h;exact hc (by simp [h])
      exact Or.inl ⟨⟨hG,by simp⟩,hrem.1.2⟩
    · right
      by_contra hD
      apply hc
      have hC:¬C.Adj x y:=by intro hC;exact hdis ⟨hC,hG,True.intro⟩
      simp [hG,hC,hD]

variable {V U E K:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

theorem marked_aux_incidence_physical_membership (tail head:E→V) (ktail khead:K→V)
    (π:Equiv.Perm V) (H₀ HK:V→U→Prop) (a:MarkedActiveEdge E K H₀ HK) (x:V⊕U)
    (hx:markedActiveAuxTail tail ktail H₀ HK a=x∨markedActiveAuxHead head khead H₀ HK a=x):
    x∈markedActivePhysicalCoin tail head ktail khead π H₀ HK a∨
      (Equiv.sumCongr π (Equiv.refl U)) x∈markedActivePhysicalCoin tail head ktail khead π H₀ HK a:=by
  rcases a with (e|e)|e
  all_goals rcases hx with hx|hx
  all_goals subst x
  all_goals simp [markedActivePhysicalCoin,markedArcPhysicalCoin,ordinaryPhysicalResource,
    markedActiveAuxTail,markedActiveAuxHead]

theorem marked_boundary_mask_changed_degree (tail head:E→V) (ktail khead:K→V)
    (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X:Finset V) (Z:Finset U) (σ τ:Sym2 (V⊕U)→Bool) (D:SimpleGraph (V⊕U))
    (hchange:∀ a:DirectedBoundaryEdge (markedActiveAuxTail tail ktail H₀ HK)
      (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z),
      σ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val)≠
        τ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val)→
      markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val∈D.edgeSet)
    (x:V⊕U):
    (Finset.univ.filter (fun a:DirectedBoundaryEdge (markedActiveAuxTail tail ktail H₀ HK)
      (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z)=>
      (markedActiveAuxTail tail ktail H₀ HK a.val=x∨markedActiveAuxHead head khead H₀ HK a.val=x)∧
      σ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val)≠
        τ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val))).card≤
      D.degree x+D.degree ((Equiv.sumCongr π (Equiv.refl U)) x):=by
  let coin:DirectedBoundaryEdge (markedActiveAuxTail tail ktail H₀ HK)
      (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z)↪Sym2 (V⊕U):=
    ⟨fun a=>markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val,
      (markedActivePhysicalCoin_injective tail head ktail khead π H₀ HK hp).comp Subtype.val_injective⟩
  apply physical_coin_incidence_card coin D
  intro a ha
  obtain ⟨_,hx,hc⟩:=Finset.mem_filter.mp ha
  exact ⟨hchange a hc,marked_aux_incidence_physical_membership tail head ktail khead π H₀ HK a.val x hx⟩

end Oberwolfach
