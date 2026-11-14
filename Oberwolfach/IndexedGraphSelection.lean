module

public import Oberwolfach.SelectionCandidateBudget

@[expose] public section

/-! Simultaneous graph selection indexed by actual outside vertices.
The index change is bijective and preserves all support multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_degree_selection_indexed (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J],
      N≤Fintype.card V→∀ (d:ℕ) (G:SimpleGraph V) (S:J→Finset V) (family:J→Set (SimpleGraph V)),
      (∀ i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card V)→
      (∀ v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ)≤p*Fintype.card V)→
      (∀ i,∀ K:SimpleGraph V,K≤spanningRestriction G (S i)→
        (∀ v,(K.degree v:ℝ)≤d*(p*Real.sqrt p*Fintype.card V)+
          d*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
        ∃ C:SimpleGraph V,C∈family i ∧ C≤spanningRestriction G (S i) ∧
          (∀ v,C.degree v≤d) ∧ Disjoint C K)→
      ∃ C:J→SimpleGraph V,
        (∀ i,C i∈family i ∧ C i≤spanningRestriction G (S i) ∧ ∀ v,(C i).degree v≤d) ∧
        (∀ i j,i≠j→Disjoint (C i) (C j)) ∧
        ∀ v,((⨆ i,C i).degree v:ℝ)≤d*(p*Fintype.card V):=by
  obtain ⟨N,_hN,hN⟩:=bounded_degree_selection_from_single_copy p hp
  refine ⟨N,?_⟩
  intro V J _ _ _ _ hn d G S family hinter hmem hsingle
  let e:Fin (Fintype.card J)≃J:=(Fintype.equivFin J).symm
  have hmem' (v:V):((Finset.univ.filter (fun i=>v∈S (e i))).card:ℝ)≤p*Fintype.card V:=by
    have he:(Finset.univ.filter (fun i=>v∈S (e i))).card=
        (Finset.univ.filter (fun i=>v∈S i)).card:=by
      apply Finset.card_bij (fun i _=>e i)
      · intro i hi;simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj heq;exact e.injective heq
      · intro j hj;exact ⟨e.symm j,by simpa using hj,by simp⟩
    rw [he];exact hmem v
  obtain ⟨C,hC,hdis,hdeg⟩:=hN V hn (Fintype.card J) d G (fun i=>S (e i))
    (fun i=>family (e i)) (fun i j hij=>hinter _ _ (fun h=>hij (e.injective h))) hmem'
    (fun i=>hsingle (e i))
  refine ⟨fun i=>C (e.symm i),?_,?_,?_⟩
  · intro i;simpa using hC (e.symm i)
  · intro i j hij;exact hdis _ _ (fun h=>hij (e.symm.injective h))
  · intro v
    have hle:(⨆ i,C (e.symm i))≤⨆ i,C i:=by
      intro x y h
      obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp h
      exact SimpleGraph.iSup_adj.mpr ⟨e.symm i,hi⟩
    exact (Nat.cast_le.mpr (SimpleGraph.degree_le_of_le hle)).trans (hdeg v)

end Oberwolfach
