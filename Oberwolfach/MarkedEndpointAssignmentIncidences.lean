module

public import Oberwolfach.MarkedEndpointPairingWitness
public import Oberwolfach.PhysicalSpokeDeletion

@[expose] public section

/-! The incidence bounds needed for simultaneous boundary paths follow
from the selected physical endpoint graphs. No injectivity of the endpoint
labels is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U J:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    [Fintype J] [DecidableEq J]
    {A₀ A₁ X₀ X₁:J→Finset V} {Y₀ Y₁:J→Finset U}
    {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}

namespace MarkedEndpointPairing

def assignedHub (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):U:=taggedHubEmbedding (Y₀ i.1) (Y₁ i.1) (P i.1).hubs_disjoint i.2

def assignedOutgoing (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):V:=taggedSubsetValue (X₀ i.1) (X₁ i.1) ((P i.1).outgoing.symm i.2)

def assignedIncoming (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):V:=taggedSubsetValue (A₀ i.1) (A₁ i.1) ((P i.1).incoming.symm i.2)

theorem assigned_hub_index_injective
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b):
    Function.Injective (fun i:Σ j,Y₀ j⊕Y₁ j=>(i.1,assignedHub P i)):=by
  rintro ⟨j,y⟩ ⟨k,z⟩ he
  have hj:=congrArg Prod.fst he
  dsimp only at hj
  subst k
  have hy:=congrArg Prod.snd he
  exact congrArg (Sigma.mk j) ((taggedHubEmbedding (Y₀ j) (Y₁ j) (P j).hubs_disjoint).injective hy)

theorem assigned_endpoint_edges
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):
    (P i.1).graph.Adj (Sum.inl (assignedOutgoing P i)) (Sum.inr (assignedHub P i))∧
    (P i.1).graph.Adj (Sum.inl (assignedIncoming P i)) (Sum.inr (assignedHub P i)):=by
  constructor
  · exact ⟨i.2,rfl,Or.inr rfl⟩
  · exact ⟨i.2,rfl,Or.inl rfl⟩

theorem assigned_same_hub_endpoints_disjoint
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (hcross:∀ j k,j≠k→Disjoint (P j).graph (P k).graph)
    (i k:Σ j,Y₀ j⊕Y₁ j) (hne:i≠k) (hu:assignedHub P i=assignedHub P k):
    Disjoint ({assignedOutgoing P i,assignedIncoming P i}:Finset V)
      {assignedOutgoing P k,assignedIncoming P k}:=by
  have hj:i.1≠k.1:=fun he=>hne (assigned_hub_index_injective P (Prod.ext he hu))
  apply Finset.disjoint_left.mpr
  intro v hi hk
  have hi':(P i.1).graph.Adj (Sum.inl v) (Sum.inr (assignedHub P i)):=by
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact (assigned_endpoint_edges P i).1
    · rw [Finset.mem_singleton.mp hi];exact (assigned_endpoint_edges P i).2
  have hk':(P k.1).graph.Adj (Sum.inl v) (Sum.inr (assignedHub P i)):=by
    rw [hu]
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (assigned_endpoint_edges P k).1
    · rw [Finset.mem_singleton.mp hk];exact (assigned_endpoint_edges P k).2
  exact disjoint_graphs_no_common_edge _ _ (hcross _ _ hj) _ _ hi' hk'

theorem assigned_endpoint_occurrences
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (hcross:∀ j k,j≠k→Disjoint (P j).graph (P k).graph) (v:V):
    (Finset.univ.filter (fun i:Σ j,Y₀ j⊕Y₁ j=>v=assignedOutgoing P i∨v=assignedIncoming P i)).card≤
      (⨆ j,(P j).graph).degree (Sum.inl v):=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun i=>Sum.inr (assignedHub P i))
  · intro i hi
    simp only [Finset.mem_coe,SimpleGraph.mem_neighborFinset]
    apply SimpleGraph.iSup_adj.mpr
    refine ⟨i.1,?_⟩
    rcases (Finset.mem_filter.mp hi).2 with rfl|rfl
    · exact (assigned_endpoint_edges P i).1
    · exact (assigned_endpoint_edges P i).2
  · intro i hi k hk he
    by_contra hne
    have hd:=assigned_same_hub_endpoints_disjoint P hcross i k hne (Sum.inr.inj he)
    exact Finset.disjoint_left.mp hd
      (by simpa using (Finset.mem_filter.mp hi).2) (by simpa using (Finset.mem_filter.mp hk).2)

theorem assigned_hub_occurrences
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (hcross:∀ j k,j≠k→Disjoint (P j).graph (P k).graph) (u:U):
    (Finset.univ.filter (fun i:Σ j,Y₀ j⊕Y₁ j=>assignedHub P i=u)).card≤
      (⨆ j,(P j).graph).degree (Sum.inr u):=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun i=>Sum.inl (assignedOutgoing P i))
  · intro i hi
    simp only [Finset.mem_coe,SimpleGraph.mem_neighborFinset]
    apply SimpleGraph.iSup_adj.mpr
    refine ⟨i.1,?_⟩
    rw [←(Finset.mem_filter.mp hi).2]
    exact ((assigned_endpoint_edges P i).1).symm
  · intro i hi k hk he
    by_contra hne
    have hu:assignedHub P i=assignedHub P k:=(Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm
    have hd:=assigned_same_hub_endpoints_disjoint P hcross i k hne hu
    exact Finset.disjoint_left.mp hd (Finset.mem_insert_self (assignedOutgoing P i) _)
      (by rw [Sum.inl.inj he];exact Finset.mem_insert_self _ _)

theorem assigned_root_spokes_injective
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (x:J↪V):Function.Injective (fun i:Σ j,Y₀ j⊕Y₁ j=>(x i.1,assignedHub P i)):=by
  intro i k he
  exact assigned_hub_index_injective P (Prod.ext (x.injective (congrArg Prod.fst he)) (congrArg (fun t:V×U=>t.2) he))

end MarkedEndpointPairing
end Oberwolfach
