module

public import Oberwolfach.SeparatedTransformerPaths

@[expose] public section

/-! The rim-edge and spoke-edge paths of the ordinary transformer are
selected in one construction. Their internal labels avoid all old roots
and all conflict neighbours of those roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq J]

 theorem ordinary_transformer_edge_paths (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W R:Finset V) (x y x' y':E→V) (v v':J→V) (u u':J→U)
    (hR:∀ i,x i∈R∧y i∈R∧x' i∈R∧y' i∈R) (hR':∀ j,v j∈R∧v' j∈R)
    (hRF:∀ i,∀ a∈({x i,y i,x' i,y' i}:Finset V),
      ∀ c∈({x i,y i,x' i,y' i}:Finset V),¬F.Adj a c)
    (hSF:∀ j,¬F.Adj (v j) (v' j))
    (r:ℕ) (hr:4≤r) (L b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ a c,b≤((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hspoke:∀ j a c,b≤(((A.filter (fun w=>H w (u j)∧H w (u' j)))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hthree:r=4→∀ i,∀ a∈A,b≤(((A∩Q.neighborFinset a)∩Q.neighborFinset (y i)∩Q.neighborFinset (y' i)).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+(Fintype.card E+Fintype.card J)*(r-1:ℕ)+r+7)*(L+1)<b):
    ∃ p:(E⊕J)→(Σ a:V,Σ c:V,Q.Walk a c),
      (∀ i,(p i).2.2.IsPath ∧
        (∀ a∈(p i).2.2.support,a∈A∧a∉W∧a∉R∧∀ c∈R,¬F.Adj a c) ∧
        (∀ a∈(p i).2.2.support,∀ c∈(p i).2.2.support,¬F.Adj a c)) ∧
      (∀ i,(p (.inl i)).2.2.length=r-3 ∧
        Q.Adj (x i) (p (.inl i)).1 ∧ Q.Adj (x' i) (p (.inl i)).1 ∧
        Q.Adj (y i) (p (.inl i)).2.1 ∧ Q.Adj (y' i) (p (.inl i)).2.1) ∧
      (∀ j,(p (.inr j)).2.2.length=r-2 ∧
        Q.Adj (v j) (p (.inr j)).1 ∧ Q.Adj (v' j) (p (.inr j)).1 ∧
        Q.Adj (v j) (p (.inr j)).2.1 ∧ Q.Adj (v' j) (p (.inr j)).2.1 ∧
        ∀ a∈(p (.inr j)).2.2.support,H a (u j)∧H a (u' j)) ∧
      ∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset ∧
        (∀ a∈(p i).2.2.support,∀ c∈(p j).2.2.support,¬F.Adj a c):=by
  let B:=W∪(R∪R.biUnion (fun a=>F.neighborFinset a))
  let C:E⊕J→Finset V:=Sum.elim (fun _=>A) (fun j=>A.filter (fun w=>H w (u j)∧H w (u' j)))
  let a:E⊕J→V:=Sum.elim x v
  let c:E⊕J→V:=Sum.elim y v
  let a':E⊕J→V:=Sum.elim x' v'
  let c':E⊕J→V:=Sum.elim y' v'
  let Z:E⊕J→Finset V:=fun i=>{a i,c i,a' i,c' i}
  let k:E⊕J→ℕ:=Sum.elim (fun _=>r) (fun _=>r+1)
  have hBC:(B.card:ℝ)≤W.card+R.card*(L+1):=by
    have hh:=forbidden_used_neighbours_card F R L hF
    have hu:(B.card:ℝ)≤W.card+(R∪R.biUnion (fun a=>F.neighborFinset a)).card:=by exact_mod_cast Finset.card_union_le _ _
    linarith only [hh,hu]
  have hZsize (i:E⊕J):(Z i).card≤4:=by
    have h1:=Finset.card_insert_le (a i) ({c i,a' i,c' i}:Finset V)
    have h2:=Finset.card_insert_le (c i) ({a' i,c' i}:Finset V)
    have h3:=Finset.card_insert_le (a' i) ({c' i}:Finset V)
    simp only [Finset.card_singleton] at h3
    dsimp only [Z];omega
  have hZind (i:E⊕J):∀ s∈Z i,∀ t∈Z i,¬F.Adj s t:=by
    cases i with
    | inl i=>exact hRF i
    | inr j=>
      intro s hs t ht
      have hs':s=v j∨s=v' j:=by simpa [Z,a,c,a',c'] using hs
      have ht':t=v j∨t=v' j:=by simpa [Z,a,c,a',c'] using ht
      rcases hs' with rfl|rfl <;> rcases ht' with rfl|rfl
      · exact F.loopless.irrefl _
      · exact hSF j
      · exact fun h=>hSF j h.symm
      · exact F.loopless.irrefl _
  have hb (i:E⊕J):(B.card:ℝ)+Fintype.card (E⊕J)*(r-1:ℕ)*(L+1)+((Z i).card+k i+2)*(L+1)<b:=by
    have hz:((Z i).card:ℝ)≤4:=by exact_mod_cast hZsize i
    have hk:(k i:ℝ)≤r+1:=by cases i <;> simp [k]
    have hh:=mul_le_mul_of_nonneg_right (show ((Z i).card:ℝ)+k i+2≤r+7 by linarith) (show 0≤L+1 by linarith)
    rw [Fintype.card_sum,Nat.cast_add]
    nlinarith only [hBC,hh,hbudget]
  have hroots (i:E⊕J):a i∈Z i∧c i∈Z i∧a' i∈Z i∧c' i∈Z i:=by simp [Z]
  have hcount' (i:E⊕J):∀ s∈(Finset.univ:Finset V),∀ t∈(Finset.univ:Finset V),
      b≤((C i∩Q.neighborFinset s∩Q.neighborFinset t).card:ℝ):=by
    intro s _ t _
    cases i with
    | inl i=>exact hcount s t
    | inr j=>exact hspoke j s t
  have hthree' (i:E⊕J):k i=4→∀ s∈C i,
      b≤(((C i∩Q.neighborFinset s)∩Q.neighborFinset (c i)∩Q.neighborFinset (c' i)).card:ℝ):=by
    cases i with
    | inl i=>exact fun he=>hthree he i
    | inr j=>intro he;dsimp [k] at he;omega
  obtain ⟨p,hp,hdis⟩:=separated_transformer_paths Q F C B Finset.univ Z
    (fun _=>Finset.subset_univ _) a c a' c' hroots (fun _=>by simp) hZind k (r-1)
    (fun i=>by cases i <;> simp [k] <;> omega) (fun i=>by cases i <;> simp [k] <;> omega)
    L b hL hF hcount' hthree' hb
  refine ⟨p,?_,?_,?_,hdis⟩
  · intro i
    have hi:=hp i
    refine ⟨hi.1,?_,hi.2.2.2.2.2.2.2.1⟩
    intro t ht
    have hclass:=hi.2.2.2.2.2.2.1 t ht
    have htA:t∈A:=by
      cases i with
      | inl i=>exact hclass.1
      | inr j=>exact (Finset.mem_filter.mp hclass.1).1
    refine ⟨htA,fun h=>hclass.2.1 (Finset.mem_union_left _ h),
      fun h=>hclass.2.1 (Finset.mem_union_right _ (Finset.mem_union_left _ h)),?_⟩
    intro s hs h
    exact hclass.2.1 (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨s,hs,(F.mem_neighborFinset s t).mpr h.symm⟩)))
  · intro i
    exact ⟨(hp (.inl i)).2.1,(hp (.inl i)).2.2.1,(hp (.inl i)).2.2.2.1,
      (hp (.inl i)).2.2.2.2.1,(hp (.inl i)).2.2.2.2.2.1⟩
  · intro j
    have hj:=hp (.inr j)
    refine ⟨?_,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,?_⟩
    · have hh:=hj.2.1;dsimp only [k,Sum.elim_inr] at hh;omega
    · intro t ht
      exact (Finset.mem_filter.mp (hj.2.2.2.2.2.2.1 t ht).1).2

end Oberwolfach
