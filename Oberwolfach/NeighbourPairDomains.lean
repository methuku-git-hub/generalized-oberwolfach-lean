module

public import Oberwolfach.NeighbourPairAssignment
public import Oberwolfach.InducedDomainCounts

@[expose] public section

/-! The neighbour assignment on the actual finite row and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem finite_domain_predicate_card (A:Finset V) (P:V→Prop) :
    (Finset.univ.filter (fun x:A=>P x.val)).card=(A.filter P).card := by
  have he:(Finset.univ.filter (fun x:A=>P x.val)).map ⟨Subtype.val,Subtype.val_injective⟩=A.filter P:=by
    ext x
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨y,hy,rfl⟩;exact ⟨y.property,hy⟩
    · intro hx;exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  rw [←he,Finset.card_map]

theorem ordinary_neighbour_pairs_on_domains (lam:ℝ) (hlam:0<lam) :
    ∀ b:ℕ,∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],∀ (S:Finset V) (T:Finset U),N≤T.card → S.card=2*T.card →
      ∀ (H:V→U→Prop) (F:SimpleGraph V),
      (∀ x∈S,lam*T.card≤((T.filter (H x)).card:ℝ)) →
      (∀ u∈T,2*lam*T.card≤((S.filter (fun x=>H x u)).card:ℝ)) →
      (∀ x,F.degree x≤b) →
      (∀ X⊆S,∀ Y⊆T,lam/16*T.card≤(X.card:ℝ) → lam/16*T.card≤(Y.card:ℝ) →
        lam*X.card*Y.card≤(bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) X Y:ℝ)) →
      ∃ (v w:Fin T.card→V) (u:Fin T.card→U),
        Function.Injective u ∧ (∀ i,u i∈T) ∧ (∀ z∈T,∃ i,u i=z) ∧
        (∀ i,v i∈S∧w i∈S∧H (v i) (u i)∧H (w i) (u i)∧¬F.Adj (v i) (w i)) ∧
        (∀ i,v i≠w i) ∧
        (∀ i j,i≠j → Disjoint ({v i,w i}:Finset V) {v j,w j}) ∧
        (∀ x,x∈S ↔ ∃ i,x=v i∨x=w i) := by
  intro b
  obtain ⟨N,hN⟩:=ordinary_neighbour_pair_assignment lam hlam b
  refine ⟨N,?_⟩
  intro V U _ _ _ _ S T hn hST H F hrow hcol hF hcut
  let e:T≃Fin T.card:=(Fintype.equivFin T).trans (finCongr (Fintype.card_coe T))
  let fS:S↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let fT:T↪U:=⟨Subtype.val,Subtype.val_injective⟩
  have hcut' (X:Finset S) (Y:Finset T)
      (hX:lam/16*T.card≤(X.card:ℝ)) (hY:lam/16*T.card≤(Y.card:ℝ)) :
      lam*X.card*Y.card≤(bipartiteMatrixCut (fun x:S=>fun u:T=>if H x.val u.val then 1 else 0) X Y:ℝ):=by
    have hh:=hcut (X.map fS) (by rintro x hx;obtain ⟨z,_,rfl⟩:=Finset.mem_map.mp hx;exact z.property)
      (Y.map fT) (by rintro u hu;obtain ⟨z,_,rfl⟩:=Finset.mem_map.mp hu;exact z.property)
      (by simpa using hX) (by simpa using hY)
    simpa only [Finset.card_map,bipartiteMatrixCut,Finset.sum_map,fS,fT,Function.Embedding.coeFn_mk] using hh
  obtain ⟨v,w,hvw,hdis,hcover⟩:=hN S T T.card hn (by simpa using hST) (Fintype.card_coe T)
    (fun x:S=>fun u:T=>H x.val u.val) (F.comap Subtype.val)
    (fun x=>by rw [finite_domain_predicate_card];exact hrow x.val x.property)
    (fun u=>by simpa only [finite_domain_predicate_card S (fun x=>H x u.val)] using hcol u.val u.property)
    (fun x=>(embedding_comap_degree_le fS F x).trans (hF x.val)) hcut'
  let u:Fin T.card→U:=fun i=>(e.symm i).val
  let v':Fin T.card→V:=fun i=>(v (e.symm i)).val
  let w':Fin T.card→V:=fun i=>(w (e.symm i)).val
  have hvw' (i:Fin T.card):v' i≠w' i:=by
    intro he
    exact Set.disjoint_left.mp hdis ⟨e.symm i,rfl⟩ ⟨e.symm i,Subtype.ext he.symm⟩
  have hv_inj:Function.Injective v':=Subtype.val_injective.comp (v.injective.comp e.symm.injective)
  have hw_inj:Function.Injective w':=Subtype.val_injective.comp (w.injective.comp e.symm.injective)
  have hcross (i j:Fin T.card):v' i≠w' j:=by
    intro he
    exact Set.disjoint_left.mp hdis ⟨e.symm i,rfl⟩ ⟨e.symm j,Subtype.ext he.symm⟩
  refine ⟨v',w',u,Subtype.val_injective.comp e.symm.injective,fun i=>(e.symm i).property,?_,?_,hvw',?_,?_⟩
  · intro z hz
    exact ⟨e ⟨z,hz⟩,by simp [u]⟩
  · intro i
    exact ⟨(v (e.symm i)).property,(w (e.symm i)).property,(hvw (e.symm i)).1,
      (hvw (e.symm i)).2.1,(hvw (e.symm i)).2.2⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with ha|ha <;> rcases hb with hb|hb
    · exact hij (hv_inj (ha.symm.trans hb))
    · exact hcross i j (ha.symm.trans hb)
    · exact hcross j i (hb.symm.trans ha)
    · exact hij (hw_inj (ha.symm.trans hb))
  · intro x
    constructor
    · intro hx
      rcases hcover ⟨x,hx⟩ with ⟨y,hy⟩|⟨y,hy⟩
      · exact ⟨e y,Or.inl (by simpa [v'] using (congrArg Subtype.val hy).symm)⟩
      · exact ⟨e y,Or.inr (by simpa [w'] using (congrArg Subtype.val hy).symm)⟩
    · rintro ⟨i,he|he⟩
      · rw [he];exact (v (e.symm i)).property
      · rw [he];exact (w (e.symm i)).property

end Oberwolfach
