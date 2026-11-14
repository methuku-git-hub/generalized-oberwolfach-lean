module

public import Oberwolfach.BoundedDegreeSelection

@[expose] public section
/-! Keep the actual factor witnesses when the bounded-degree selection lemma
chooses their physical graphs. Different root types may use different
witness types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_degree_selection_with_witnesses (p:ℝ) (hp:0<p):
    ∃n₀:ℕ,2≤n₀ ∧ ∀(V:Type) [Fintype V] [DecidableEq V],n₀≤Fintype.card V→
    ∀(N D:ℕ) (G:SimpleGraph V) (S:Fin N→Finset V)
      (Choice:Fin N→Type) (Valid:∀i,Choice i→Prop) (graph:∀i,Choice i→SimpleGraph V),
    (∀i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card V) →
    (∀v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ)≤p*Fintype.card V) →
    (∀i,∀J:SimpleGraph V,J≤spanningRestriction G (S i)→
      (∀v,(J.degree v:ℝ)≤D*(p*Real.sqrt p*Fintype.card V))→
      ∃C:Fin (Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)))→Choice i,
        (∀a,Valid i (C a) ∧ graph i (C a)≤spanningRestriction G (S i) ∧
          (∀v,(graph i (C a)).degree v≤D) ∧ Disjoint (graph i (C a)) J) ∧
        (∀a b,a≠b→Disjoint (graph i (C a)) (graph i (C b)))) →
    ∃C:∀i,Choice i,
      (∀i,Valid i (C i) ∧ graph i (C i)≤spanningRestriction G (S i) ∧ ∀v,(graph i (C i)).degree v≤D) ∧
      (∀i j,i≠j→Disjoint (graph i (C i)) (graph j (C j))) ∧
      (∀v,((⨆i,graph i (C i)).degree v:ℝ)≤D*(p*Fintype.card V)):=by
  obtain ⟨n₀,hn₀,hselect⟩:=bounded_degree_selection p hp
  refine ⟨n₀,hn₀,?_⟩
  intro V _ _ hn N D G S Choice Valid graph hinter hmem hrich
  let family:Fin N→Set (SimpleGraph V):=fun i F=>∃c:Choice i,Valid i c∧graph i c=F
  have hcandidates:∀i,∀J:SimpleGraph V,J≤spanningRestriction G (S i)→
      (∀v,(J.degree v:ℝ)≤D*(p*Real.sqrt p*Fintype.card V))→
      ∃C:Fin (Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)))→SimpleGraph V,
        (∀a,C a∈family i ∧ C a≤spanningRestriction G (S i) ∧
          (∀v,(C a).degree v≤D) ∧ Disjoint (C a) J) ∧
        (∀a b,a≠b→Disjoint (C a) (C b)):=by
    intro i J hJ hdegree
    obtain ⟨C,hC,hdis⟩:=hrich i J hJ hdegree
    refine ⟨fun a=>graph i (C a),?_,hdis⟩
    intro a
    exact ⟨⟨C a,(hC a).1,rfl⟩,(hC a).2⟩
  obtain ⟨F,hF,hdis,hdeg⟩:=hselect V hn N D G S family hinter hmem hcandidates
  have hex:∀i,∃c:Choice i,Valid i c∧graph i c=F i:=fun i=>(hF i).1
  let C:∀i,Choice i:=fun i=>Classical.choose (hex i)
  have hC (i:Fin N):Valid i (C i) ∧ graph i (C i)=F i:=Classical.choose_spec (hex i)
  refine ⟨C,?_,?_,?_⟩
  · intro i
    rw [(hC i).2]
    exact ⟨(hC i).1,(hF i).2⟩
  · intro i j hij
    rw [(hC i).2,(hC j).2]
    exact hdis i j hij
  · intro v
    have he:(⨆i,graph i (C i))=⨆i,F i:=by congr 1;funext i;exact (hC i).2
    rw [he]
    exact hdeg v
end Oberwolfach
