module

public import Oberwolfach.IndexedGraphSelection

@[expose] public section
/-! Simultaneously select bounded-degree supported graphs while avoiding a fixed
physical graph, charging its degree in each local selection budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_degree_selection_indexed_avoiding (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J],
      N≤Fintype.card V→∀ (d:ℕ) (G K₀:SimpleGraph V) (δ:ℝ)
      (S:J→Finset V) (family:J→Set (SimpleGraph V)),
      (∀v,(K₀.degree v:ℝ)≤δ)→
      (∀ i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card V)→
      (∀ v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ)≤p*Fintype.card V)→
      (∀ i,∀ K:SimpleGraph V,K≤spanningRestriction G (S i)→
        (∀ v,(K.degree v:ℝ)≤d*(p*Real.sqrt p*Fintype.card V)+
          d*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ)+δ)→
        ∃ C:SimpleGraph V,C∈family i ∧ C≤spanningRestriction G (S i) ∧
          (∀ v,C.degree v≤d) ∧ Disjoint C K)→
      ∃ C:J→SimpleGraph V,
        (∀ i,C i∈family i ∧ C i≤spanningRestriction G (S i) ∧
          (∀ v,(C i).degree v≤d) ∧ Disjoint (C i) K₀) ∧
        (∀ i j,i≠j→Disjoint (C i) (C j)) ∧
        ∀ v,((⨆ i,C i).degree v:ℝ)≤d*(p*Fintype.card V):=by
  obtain ⟨N,hN⟩:=bounded_degree_selection_indexed p hp
  refine ⟨N,?_⟩
  intro V J _ _ _ _ hn d G K₀ δ S family hK₀ hinter hmem hsingle
  let family':J→Set (SimpleGraph V):=fun i C=>C∈family i ∧ Disjoint C K₀
  have hsingle':∀i,∀K:SimpleGraph V,K≤spanningRestriction G (S i)→
      (∀v,(K.degree v:ℝ)≤d*(p*Real.sqrt p*Fintype.card V)+
        d*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
      ∃C:SimpleGraph V,C∈family' i ∧ C≤spanningRestriction G (S i) ∧
        (∀v,C.degree v≤d) ∧ Disjoint C K:=by
    intro i K hK hdegK
    let K₁:=spanningRestriction (K₀⊓G) (S i)
    have hK₁G:K₁≤spanningRestriction G (S i):=by
      intro a b hab
      have hh:=(spanningRestriction_adj _ _ _ _).mp hab
      exact (spanningRestriction_adj G (S i) a b).mpr ⟨hh.1.2,hh.2⟩
    have hK₁:K₁≤K₀:=by intro a b hab;exact ((spanningRestriction_adj _ _ _ _).mp hab).1.1
    have hdeg (v:V):((K⊔K₁).degree v:ℝ)≤d*(p*Real.sqrt p*Fintype.card V)+
        d*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ)+δ:=by
      have hh:((K⊔K₁).degree v:ℝ)≤(K.degree v:ℝ)+K₁.degree v:=by
        exact_mod_cast graph_degree_sup_le K K₁ v
      have hk:((K₁.degree v):ℝ)≤δ:=by
        have hh:((K₁.degree v):ℝ)≤K₀.degree v:=by exact_mod_cast (SimpleGraph.degree_le_of_le hK₁ (v:=v))
        exact hh.trans (hK₀ v)
      exact hh.trans (add_le_add (hdegK v) hk)
    obtain ⟨C,hC,hCG,hCdeg,hdis⟩:=hsingle i (K⊔K₁) (sup_le hK hK₁G)
      (by intro v;convert hdeg v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    have havoid:Disjoint C K₀:=by
      apply disjoint_iff_inf_le.mpr
      intro a b hab
      have hs:=(spanningRestriction_adj G (S i) a b).mp (hCG hab.1)
      have hK₁ab:K₁.Adj a b:=(spanningRestriction_adj _ _ _ _).mpr ⟨⟨hab.2,hs.1⟩,hs.2⟩
      exact (disjoint_iff_inf_le.mp hdis) (v:=a) (w:=b) ⟨hab.1,Or.inr hK₁ab⟩
    exact ⟨C,⟨hC,havoid⟩,hCG,hCdeg,hdis.mono_right le_sup_left⟩
  obtain ⟨C,hC,hdis,hdeg⟩:=hN V J hn d G S family' hinter hmem hsingle'
  refine ⟨C,?_,hdis,hdeg⟩
  intro i
  exact ⟨(hC i).1.1,(hC i).2.1,(hC i).2.2,(hC i).1.2⟩
end Oberwolfach
