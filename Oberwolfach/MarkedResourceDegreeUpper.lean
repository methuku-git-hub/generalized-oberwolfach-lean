module

public import Oberwolfach.MarkedPhysicalGraphLeftover

@[expose] public section

/-! Count physical resources by their actual neighbours. The two-element
condition excludes degenerate rim resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_incident_card_le_graph_degree (G:SimpleGraph (V⊕U))
    (S:Finset (Finset V⊕(V×U)))
    (hpairs:∀ e,Sum.inl e∈S→e.card=2)
    (hrim:∀ v w,Sum.inl ({v,w}:Finset V)∈S→G.Adj (Sum.inl v) (Sum.inl w))
    (hspoke:∀ v u,Sum.inr (v,u)∈S→G.Adj (Sum.inl v) (Sum.inr u))
    (x:V⊕U):
    (S.filter (markedPhysicalIncident x)).card≤G.degree x:=by
  have hsub:S.filter (markedPhysicalIncident x)⊆(G.neighborFinset x).image (markedPairResource x):=by
    intro e he
    obtain ⟨hmem,hi⟩:=Finset.mem_filter.mp he
    cases x with
    | inl v=>
      cases e with
      | inl e=>
        obtain ⟨a,b,hab,rfl⟩:=Finset.card_eq_two.mp (hpairs e hmem)
        have hv:v=a∨v=b:=by simpa only [markedPhysicalIncident,Finset.mem_insert,Finset.mem_singleton] using hi
        rcases hv with hv|hv
        · subst v
          exact Finset.mem_image.mpr ⟨Sum.inl b,(G.mem_neighborFinset _ _).mpr (hrim a b hmem),rfl⟩
        · subst v
          refine Finset.mem_image.mpr ⟨Sum.inl a,(G.mem_neighborFinset _ _).mpr (hrim a b hmem).symm,?_⟩
          simp only [markedPairResource,Finset.pair_comm]
      | inr z=>
        have hz:z.1=v:=hi
        refine Finset.mem_image.mpr ⟨Sum.inr z.2,(G.mem_neighborFinset _ _).mpr (hz ▸ hspoke z.1 z.2 hmem),?_⟩
        exact congrArg Sum.inr (Prod.ext hz.symm rfl)
    | inr u=>
      cases e with
      | inl e=>exact False.elim hi
      | inr z=>
        have hz:z.2=u:=hi
        refine Finset.mem_image.mpr ⟨Sum.inl z.1,(G.mem_neighborFinset _ _).mpr (hz ▸ (hspoke z.1 z.2 hmem).symm),?_⟩
        exact congrArg Sum.inr (Prod.ext rfl hz.symm)
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (G.card_neighborFinset_eq_degree x).le)

end Oberwolfach
