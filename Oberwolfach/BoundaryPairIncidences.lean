module

public import Oberwolfach.TypedEndpointPairing

@[expose] public section

/-! Incidence and disjointness estimates for the prescribed triples
obtained from the selected endpoint assignments at all exterior roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U J:Type} [Fintype V] [Fintype U] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq J]

theorem disjoint_embedding_pair_unique {A:Finset V} {B:Finset U}
    (v w:B↪A) (hdis:Disjoint (Set.range v) (Set.range w)) (a:V) (u z:B)
    (hu:a=(v u).val∨a=(w u).val) (hz:a=(v z).val∨a=(w z).val):u=z:=by
  rcases hu with hu|hu <;> rcases hz with hz|hz
  · exact v.injective (Subtype.ext (hu.symm.trans hz))
  · exact (Set.disjoint_left.mp hdis ⟨u,rfl⟩ ⟨z,Subtype.ext (hz.symm.trans hu)⟩).elim
  · exact (Set.disjoint_left.mp hdis ⟨z,rfl⟩ ⟨u,Subtype.ext (hu.symm.trans hz)⟩).elim
  · exact w.injective (Subtype.ext (hu.symm.trans hz))

theorem boundary_pair_incidences (X:Finset V) (x:J↪V)
    (A:J→Finset V) (B:J→Finset U) (v w:∀ j,B j↪A j)
    (hx:∀ j,x j∉X) (hA:∀ j,A j⊆X)
    (hdis:∀ j,Disjoint (Set.range (v j)) (Set.range (w j)))
    (P:J→SimpleGraph (V⊕U))
    (hP:∀ j,∀ z:B j,
      (P j).Adj (Sum.inl (v j z).val) (Sum.inr z.val) ∧
      (P j).Adj (Sum.inl (w j z).val) (Sum.inr z.val))
    (hcross:∀ i j,i≠j→Disjoint (P i) (P j))
    (D:ℕ) (hsize:∀ j,(B j).card≤D)
    (hmemA:∀ a,(Finset.univ.filter (fun j=>a∈A j)).card≤D)
    (hmemB:∀ u,(Finset.univ.filter (fun j=>u∈B j)).card≤D):
    (∀ i j:(Σ k,B k),i≠j→x i.1=x j.1→
      Disjoint ({(v i.1 i.2).val,(w i.1 i.2).val}:Finset V)
        {(v j.1 j.2).val,(w j.1 j.2).val}) ∧
    (∀ i j:(Σ k,B k),i≠j→i.2.val=j.2.val→
      Disjoint ({x i.1,(v i.1 i.2).val,(w i.1 i.2).val}:Finset V)
        {x j.1,(v j.1 j.2).val,(w j.1 j.2).val}) ∧
    (∀ a,(Finset.univ.filter (fun i:(Σ k,B k)=>
      a∈({x i.1,(v i.1 i.2).val,(w i.1 i.2).val}:Finset V))).card≤D) ∧
    (∀ u,(Finset.univ.filter (fun i:(Σ k,B k)=>i.2.val=u)).card≤D):=by
  have hmem (i:Σ k,B k) (a:V)
      (ha:a=(v i.1 i.2).val∨a=(w i.1 i.2).val):a∈A i.1:=by
    rcases ha with rfl|rfl
    · exact (v i.1 i.2).property
    · exact (w i.1 i.2).property
  have hsame (i j:Σ k,B k) (he:i.1=j.1) (a:V)
      (hi:a=(v i.1 i.2).val∨a=(w i.1 i.2).val)
      (hj:a=(v j.1 j.2).val∨a=(w j.1 j.2).val):i=j:=by
    rcases i with ⟨k,u⟩;rcases j with ⟨l,z⟩
    dsimp only at he;subst l
    have hz:=disjoint_embedding_pair_unique (v k) (w k) (hdis k) a u z hi hj
    exact congrArg (Sigma.mk k) hz
  have hpair (i j:Σ k,B k) (hne:i≠j) (he:x i.1=x j.1):
      Disjoint ({(v i.1 i.2).val,(w i.1 i.2).val}:Finset V)
        {(v j.1 j.2).val,(w j.1 j.2).val}:=by
    apply Finset.disjoint_left.mpr
    intro a hi hj
    exact hne (hsame i j (x.injective he) a
      (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hi)
      (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hj))
  refine ⟨hpair,?_,?_,?_⟩
  · intro i j hne hu
    have hij:i.1≠j.1:=by
      intro he
      rcases i with ⟨k,u⟩;rcases j with ⟨l,z⟩
      dsimp only at he;subst l
      exact hne (congrArg (Sigma.mk k) (Subtype.ext hu))
    have hxr:x i.1≠x j.1:=fun he=>hij (x.injective he)
    apply Finset.disjoint_left.mpr
    intro a hi hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with hi|hi <;> rcases hj with hj|hj
    · exact hxr (hi.symm.trans hj)
    · exact hx i.1 (hi ▸ hA j.1 (hmem j a hj))
    · exact hx j.1 (hj ▸ hA i.1 (hmem i a hi))
    · have heI:(P i.1).Adj (Sum.inl a) (Sum.inr i.2.val):=by
        rcases hi with rfl|rfl
        · exact (hP i.1 i.2).1
        · exact (hP i.1 i.2).2
      have heJ:(P j.1).Adj (Sum.inl a) (Sum.inr i.2.val):=by
        rw [hu]
        rcases hj with rfl|rfl
        · exact (hP j.1 j.2).1
        · exact (hP j.1 j.2).2
      exact disjoint_graphs_no_common_edge _ _ (hcross i.1 j.1 hij) _ _ heI heJ
  · intro a
    by_cases ha:a∈X
    · apply le_trans _ (hmemA a)
      apply Finset.card_le_card_of_injOn (fun i:(Σ k,B k)=>i.1)
      · intro i hi
        have hai: a=(v i.1 i.2).val∨a=(w i.1 i.2).val:=by
          have hh:=(Finset.mem_filter.mp hi).2
          simp only [Finset.mem_insert,Finset.mem_singleton] at hh
          exact hh.resolve_left (fun he=>hx i.1 (he ▸ ha))
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem i a hai⟩
      · intro i hi j hj he
        apply hsame i j he a
        all_goals
          first
          | have hh:=(Finset.mem_filter.mp hi).2
            simp only [Finset.mem_insert,Finset.mem_singleton] at hh
            exact hh.resolve_left (fun hh=>hx i.1 (hh ▸ ha))
          | have hh:=(Finset.mem_filter.mp hj).2
            simp only [Finset.mem_insert,Finset.mem_singleton] at hh
            exact hh.resolve_left (fun hh=>hx j.1 (hh ▸ ha))
    · have hroot (i:Σ k,B k)
          (hi:i∈Finset.univ.filter (fun i:(Σ k,B k)=>a∈({x i.1,(v i.1 i.2).val,(w i.1 i.2).val}:Finset V))):
          a=x i.1:=by
        have hh:=(Finset.mem_filter.mp hi).2
        simp only [Finset.mem_insert,Finset.mem_singleton] at hh
        exact hh.resolve_right (fun he=>ha (hA i.1 (hmem i a he)))
      by_cases hex:∃ j,x j=a
      · obtain ⟨j,hj⟩:=hex
        apply le_trans _ (hsize j)
        apply Finset.card_le_card_of_injOn (fun i:(Σ k,B k)=>i.2.val)
        · intro i hi
          have he:i.1=j:=x.injective ((hroot i hi).symm.trans hj.symm)
          exact he ▸ i.2.property
        · intro i hi k hk he
          have hik:i.1=k.1:=x.injective ((hroot i hi).symm.trans (hroot k hk))
          rcases i with ⟨i,u⟩;rcases k with ⟨k,z⟩
          dsimp only at hik;subst k
          exact congrArg (Sigma.mk i) (Subtype.ext he)
      · have hempty:(Finset.univ.filter (fun i:(Σ k,B k)=>
            a∈({x i.1,(v i.1 i.2).val,(w i.1 i.2).val}:Finset V)))=∅:=by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi;exact hex ⟨i.1,(hroot i hi).symm⟩
        rw [hempty];simp
  · intro u
    apply le_trans _ (hmemB u)
    apply Finset.card_le_card_of_injOn (fun i:(Σ k,B k)=>i.1)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2 ▸ i.2.property⟩
    · intro i hi j hj he
      rcases i with ⟨k,a⟩;rcases j with ⟨l,b⟩
      dsimp only at he;subst l
      exact congrArg (Sigma.mk k) (Subtype.ext
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm))

end Oberwolfach
