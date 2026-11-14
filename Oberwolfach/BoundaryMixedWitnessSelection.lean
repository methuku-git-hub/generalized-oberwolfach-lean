module

public import Oberwolfach.BoundaryFactorSelectionSingle

@[expose] public section
/-! Select hub and row factor witnesses together. Their physical graphs are
pairwise disjoint across both types and their combined degree is bounded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_boundary_factor_selection (p:ℝ) (hp:0<p):
    ∃n₀:ℕ,2≤n₀ ∧ ∀(V I J:Type) [Fintype V] [Fintype I] [Fintype J]
      [DecidableEq V] [DecidableEq I] [DecidableEq J],n₀≤Fintype.card V→
    ∀(N D:ℕ) (G:SimpleGraph V) (S:Fin N→Finset V)
      (Choice:Fin N→Type) (Valid:∀i,Choice i→Prop) (graph:∀i,Choice i→SimpleGraph V)
      (x:I↪Fin N) (u:J↪Fin N) (hsep:∀i j,x i≠u j)
      (Row:I→Type) (Hub:J→Type) (rowValid:∀i,Row i→Prop) (hubValid:∀j,Hub j→Prop)
      (rowGraph:∀i,Row i→SimpleGraph V) (hubGraph:∀j,Hub j→SimpleGraph V)
      (rowOf:∀i,Choice (x i)→Row i) (hubOf:∀j,Choice (u j)→Hub j),
    (∀i c,Valid (x i) c→ rowValid i (rowOf i c) ∧ graph (x i) c=rowGraph i (rowOf i c)) →
    (∀j c,Valid (u j) c→hubValid j (hubOf j c) ∧ graph (u j) c=hubGraph j (hubOf j c)) →
    (∀i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card V) →
    (∀v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ)≤p*Fintype.card V) →
    (∀i,∀K:SimpleGraph V,K≤spanningRestriction G (S i)→
      (∀v,(K.degree v:ℝ)≤D*(p*Real.sqrt p*Fintype.card V)+
        D*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
      ∃C:Choice i,Valid i C ∧ graph i C≤spanningRestriction G (S i) ∧
        (∀v,(graph i C).degree v≤D) ∧ Disjoint (graph i C) K) →
    ∃R:∀i,Row i,∃H:∀j,Hub j,
      (∀i,rowValid i (R i)) ∧ (∀j,hubValid j (H j)) ∧
      (∀i i',i≠i'→Disjoint (rowGraph i (R i)) (rowGraph i' (R i'))) ∧
      (∀j j',j≠j'→Disjoint (hubGraph j (H j)) (hubGraph j' (H j'))) ∧
      (∀i j,Disjoint (rowGraph i (R i)) (hubGraph j (H j))) ∧
      (∀v,(((⨆i,rowGraph i (R i))⊔(⨆j,hubGraph j (H j))).degree v:ℝ)≤D*(p*Fintype.card V)):=by
  obtain ⟨n₀,hn₀,hselect⟩:=bounded_degree_selection_with_single_witness p hp
  refine ⟨n₀,hn₀,?_⟩
  intro V I J _ _ _ _ _ _ hn N D G S Choice Valid graph x u hsep Row Hub rowValid hubValid rowGraph hubGraph rowOf hubOf
    hrow hhub hinter hmem hsingle
  obtain ⟨C,hC,hdis,hdeg⟩:=hselect V hn N D G S Choice Valid graph hinter hmem hsingle
  let R:=fun i=>rowOf i (C (x i))
  let H:=fun j=>hubOf j (C (u j))
  have hr (i:I):rowValid i (R i) ∧ graph (x i) (C (x i))=rowGraph i (R i):=hrow i _ (hC (x i)).1
  have hh (j:J):hubValid j (H j) ∧ graph (u j) (C (u j))=hubGraph j (H j):=hhub j _ (hC (u j)).1
  refine ⟨R,H,fun i=>(hr i).1,fun j=>(hh j).1,?_,?_,?_,?_⟩
  · intro i i' hne
    rw [←(hr i).2,←(hr i').2]
    exact hdis (x i) (x i') (fun he=>hne (x.injective he))
  · intro j j' hne
    rw [←(hh j).2,←(hh j').2]
    exact hdis (u j) (u j') (fun he=>hne (u.injective he))
  · intro i j
    rw [←(hr i).2,←(hh j).2]
    exact hdis (x i) (u j) (hsep i j)
  · intro v
    have hsub:((⨆i,rowGraph i (R i))⊔(⨆j,hubGraph j (H j)))≤⨆k,graph k (C k):=by
      apply sup_le
      · apply iSup_le;intro i;rw [←(hr i).2];exact le_iSup (fun k=>graph k (C k)) (x i)
      · apply iSup_le;intro j;rw [←(hh j).2];exact le_iSup (fun k=>graph k (C k)) (u j)
    have hdegree:(((⨆i,rowGraph i (R i))⊔(⨆j,hubGraph j (H j))).degree v:ℝ)≤
      ((⨆k,graph k (C k)).degree v:ℝ):=by exact_mod_cast (SimpleGraph.degree_le_of_le hsub (v:=v))
    exact hdegree.trans (hdeg v)
end Oberwolfach
