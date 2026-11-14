module

public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Fintype.Powerset

@[expose] public section
/-! A single resource packing splits into disjoint physical rim-edge sets
indexed by its original hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def physicalHubRims {C U V:Type} [Fintype V] [DecidableEq V]
    (S:Finset C) (hub:C→U) (R:C→Finset (Finset V⊕(V×U))) (w:U):Finset (Finset V):=
  Finset.univ.filter (fun e=>∃c∈S,hub c=w ∧ Sum.inl e∈R c)

theorem physical_hub_rims_packed
    {C U V:Type} [Fintype V] [DecidableEq V]
    (S:Finset C) (hub:C→U) (R:C→Finset (Finset V⊕(V×U)))
    (hpack:∀c∈S,∀c'∈S,c≠c'→Disjoint (R c) (R c')):
    (∀w z,w≠z→Disjoint (physicalHubRims S hub R w) (physicalHubRims S hub R z)) ∧
    (∀c∈S,∀e,Sum.inl e∈R c→e∈physicalHubRims S hub R (hub c)):=by
  constructor
  · intro w z hne
    apply Finset.disjoint_left.mpr
    intro e he hf
    simp only [physicalHubRims,Finset.mem_filter,Finset.mem_univ,true_and] at he hf
    obtain ⟨c,hc,hw,hr⟩:=he
    obtain ⟨c',hc',hz,hr'⟩:=hf
    have hcc:c≠c':=by intro heq;apply hne;rw [←hw,←hz,heq]
    exact Finset.disjoint_left.mp (hpack c hc c' hc' hcc) hr hr'
  · intro c hc e he
    simp only [physicalHubRims,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨c,hc,rfl,he⟩
end Oberwolfach
