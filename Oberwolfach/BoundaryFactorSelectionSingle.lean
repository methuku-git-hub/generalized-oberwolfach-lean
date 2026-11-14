module

public import Oberwolfach.SelectionCandidateBudget

@[expose] public section
/-! Select actual factor witnesses with bounded union degree from the
single-factor existence supplied under every allowed deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_degree_selection_with_single_witness (p:ℝ) (hp:0<p):
    ∃n₀:ℕ,2≤n₀ ∧ ∀(V:Type) [Fintype V] [DecidableEq V],n₀≤Fintype.card V→
    ∀(N D:ℕ) (G:SimpleGraph V) (S:Fin N→Finset V)
      (Choice:Fin N→Type) (Valid:∀i,Choice i→Prop) (graph:∀i,Choice i→SimpleGraph V),
    (∀i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card V) →
    (∀v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ)≤p*Fintype.card V) →
    (∀i,∀K:SimpleGraph V,K≤spanningRestriction G (S i)→
      (∀v,(K.degree v:ℝ)≤D*(p*Real.sqrt p*Fintype.card V)+
        D*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
      ∃C:Choice i,Valid i C ∧ graph i C≤spanningRestriction G (S i) ∧
        (∀v,(graph i C).degree v≤D) ∧ Disjoint (graph i C) K) →
    ∃C:∀i,Choice i,
      (∀i,Valid i (C i) ∧ graph i (C i)≤spanningRestriction G (S i) ∧ ∀v,(graph i (C i)).degree v≤D) ∧
      (∀i j,i≠j→Disjoint (graph i (C i)) (graph j (C j))) ∧
      (∀v,((⨆i,graph i (C i)).degree v:ℝ)≤D*(p*Fintype.card V)):=by
  obtain ⟨n₀,hn₀,hselect⟩:=bounded_degree_selection_from_single_copy p hp
  refine ⟨n₀,hn₀,?_⟩
  intro V _ _ hn N D G S Choice Valid graph hinter hmem hsingle
  let family:Fin N→Set (SimpleGraph V):=fun i F=>∃c:Choice i,Valid i c∧graph i c=F
  have hcandidates:∀i,∀K:SimpleGraph V,K≤spanningRestriction G (S i)→
      (∀v,(K.degree v:ℝ)≤D*(p*Real.sqrt p*Fintype.card V)+
        D*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
      ∃C:SimpleGraph V,C∈family i ∧ C≤spanningRestriction G (S i) ∧
        (∀v,C.degree v≤D) ∧ Disjoint C K:=by
    intro i K hK hdegree
    obtain ⟨C,hC,hsub,hdeg,hdis⟩:=hsingle i K hK hdegree
    exact ⟨graph i C,⟨C,hC,rfl⟩,hsub,hdeg,hdis⟩
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
