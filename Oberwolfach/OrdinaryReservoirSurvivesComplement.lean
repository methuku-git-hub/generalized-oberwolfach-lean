module

public import Oberwolfach.OrdinaryComplementRemainderDecomposition
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! A reserved wheel reservoir remains in the actual completion host when
complement embeddings avoid its rim edges and its spoke labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reservoir_survives_complement {n q:ℕ}
    (G:SimpleGraph (Fin n)) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (fC:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Href:Fin n→Fin q→Prop) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hA:A⊆ordinaryHostResources G Href)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (G\ordinaryResourceRim G A).Adj (fC u x) (fC u y))
    (hSpoke:∀u x,¬Href (fC u x) u):
    A⊆ordinaryHostResources (G\ordinaryEmbeddedComplements Fs C fC)
      (fun v u=>v∉Set.range (fC u)):=by
  have hEmb:ordinaryEmbeddedComplements Fs C fC≤G\ordinaryResourceRim G A:=by
    apply iSup_le
    intro u x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj (fC u) _ _ _).mp hxy
    exact hRim u a b hab
  intro e he
  cases e with
  | inl e=>
    induction e using Sym2.inductionOn with
    | _ v w=>
      apply (ordinaryHostResources_rim _ _ _).mpr
      change (G\ordinaryEmbeddedComplements Fs C fC).Adj v w
      have hg:G.Adj v w:=(ordinaryHostResources_rim G Href _).mp (hA he)
      refine ⟨hg,?_⟩
      intro hemb
      have hnot:¬(ordinaryResourceRim G A).Adj v w:=(hEmb hemb).2
      exact hnot ⟨hg,he⟩
  | inr z=>
    rcases z with ⟨v,u⟩
    apply (ordinaryHostResources_spoke _ _ v u).mpr
    intro hv
    obtain ⟨x,rfl⟩:=hv
    exact hSpoke u x ((ordinaryHostResources_spoke G Href _ _).mp (hA he))
theorem ordinary_reservoir_in_target_host {n q:ℕ}
    (Reference Target:SimpleGraph (Fin n)) (Href:Fin n→Fin q→Prop)
    (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hA:A⊆ordinaryHostResources Reference Href)
    (hReserve:ordinaryResourceRim Reference A≤Target):
    A⊆ordinaryHostResources Target Href:=by
  intro e he
  cases e with
  | inl e=>
    induction e using Sym2.inductionOn with
    | _ v w=>
      apply (ordinaryHostResources_rim Target Href _).mpr
      apply hReserve
      exact ⟨(ordinaryHostResources_rim Reference Href _).mp (hA he),he⟩
  | inr z=>
    rcases z with ⟨v,u⟩
    exact (ordinaryHostResources_spoke Target Href v u).mpr
      ((ordinaryHostResources_spoke Reference Href v u).mp (hA he))

theorem ordinary_protected_reservoir_survives_complement {n q:ℕ}
    (Reference Target:SimpleGraph (Fin n)) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (fC:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Href:Fin n→Fin q→Prop) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hA:A⊆ordinaryHostResources Reference Href)
    (hReserve:ordinaryResourceRim Reference A≤Target)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\ordinaryResourceRim Reference A).Adj (fC u x) (fC u y))
    (hSpoke:∀u x,¬Href (fC u x) u):
    A⊆ordinaryHostResources (Target\ordinaryEmbeddedComplements Fs C fC)
      (fun v u=>v∉Set.range (fC u)):=by
  have heq:ordinaryResourceRim Target A=ordinaryResourceRim Reference A:=by
    apply SimpleGraph.ext
    funext v w
    apply propext
    constructor
    · rintro ⟨_,he⟩
      exact ⟨(ordinaryHostResources_rim Reference Href _).mp (hA he),he⟩
    · intro he
      exact ⟨hReserve he,he.2⟩
  apply ordinary_reservoir_survives_complement Target Fs C fC Href A
    (ordinary_reservoir_in_target_host Reference Target Href A hA hReserve)
  · intro u x y hxy
    rw [heq]
    exact hRim u x y hxy
  · exact hSpoke

end Oberwolfach
