module

public import Oberwolfach.MarkedIncidentResources
public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! Convert actual graph degrees to counts of unused physical resources.
The row and hub summands remain distinct, and each neighbour contributes
one distinct resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def markedPairResource: (V⊕U)→(V⊕U)→(Finset V⊕(V×U))
  | Sum.inl x,Sum.inl y=>Sum.inl {x,y}
  | Sum.inl x,Sum.inr u=>Sum.inr (x,u)
  | Sum.inr u,Sum.inl x=>Sum.inr (x,u)
  | Sum.inr _,Sum.inr _=>Sum.inl ∅

theorem graph_degree_le_marked_incident (G:SimpleGraph (V⊕U))
    (S:Finset (Finset V⊕(V×U))) (hU:∀ u v,¬G.Adj (Sum.inr u) (Sum.inr v))
    (hS:∀ x y,G.Adj x y→markedPairResource x y∈S) (x:V⊕U):
    G.degree x≤(S.filter (markedPhysicalIncident x)).card:=by
  let f:{y // G.Adj x y}→S.filter (markedPhysicalIncident x):=fun y=>
    ⟨markedPairResource x y.val,Finset.mem_filter.mpr ⟨hS x y.val y.property,by
      cases x <;> rcases y with ⟨(_|_),hy⟩
      all_goals simp only [markedPairResource,markedPhysicalIncident,Finset.mem_insert,
        Finset.mem_singleton,true_or]
      exact (hU _ _ hy).elim⟩⟩
  have hi:Function.Injective f:=by
    intro y z he
    have he':markedPairResource x y.val=markedPairResource x z.val:=congrArg Subtype.val he
    apply Subtype.ext
    cases x with
    | inl v=>
      rcases y with ⟨(y|y),hy⟩ <;> rcases z with ⟨(z|z),hz⟩
      · have hp:({v,y}:Finset V)={v,z}:=Sum.inl.inj he'
        have hyz:y=v∨y=z:=by
          have h:y∈({v,z}:Finset V):=hp ▸ (by simp)
          simpa only [Finset.mem_insert,Finset.mem_singleton] using h
        rcases hyz with hyz|hyz
        · exact (hy.ne (congrArg Sum.inl hyz.symm)).elim
        · exact congrArg Sum.inl hyz
      · exact (Sum.inl_ne_inr he').elim
      · exact (Sum.inr_ne_inl he').elim
      · exact congrArg Sum.inr (Prod.mk.inj (Sum.inr.inj he')).2
    | inr u=>
      rcases y with ⟨(y|y),hy⟩ <;> rcases z with ⟨(z|z),hz⟩
      · exact congrArg Sum.inl (Prod.mk.inj (Sum.inr.inj he')).1
      · exact (hU _ _ hz).elim
      · exact (hU _ _ hy).elim
      · exact (hU _ _ hy).elim
  have hc:=Fintype.card_le_of_injective f hi
  have he:Fintype.card {y // G.Adj x y}=G.degree x:=by
    convert G.card_neighborSet_eq_degree x using 1 <;> congr!
  rw [he,Fintype.card_coe] at hc
  exact hc

theorem graph_degree_le_unused_marked_incident (G:SimpleGraph (V⊕U))
    (S C:Finset (Finset V⊕(V×U))) (hU:∀ u v,¬G.Adj (Sum.inr u) (Sum.inr v))
    (hS:∀ x y,G.Adj x y→markedPairResource x y∈S∧markedPairResource x y∉C) (x:V⊕U):
    G.degree x≤((S.filter (markedPhysicalIncident x))\C).card:=by
  have h:=graph_degree_le_marked_incident G (S\C) hU
    (fun x y h=>Finset.mem_sdiff.mpr (hS x y h)) x
  convert h using 1
  congr 1
  ext e
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  tauto
end Oberwolfach
