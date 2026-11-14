module

public import Oberwolfach.MarkedPairHubRows
public import Oberwolfach.SharedTwoRootCycleGeometry

@[expose] public section

/-! Realise all rim-wheel hubs after the paths and four attachment requests
have been fixed. The c+6 bound is derived from their actual vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]

 theorem marked_rim_wheel_hubs
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b n:ℕ) (v w v' w':I→V)
    (p:I→(Fin n↪V)) (ρ:I→Equiv.Perm (Fin (n+2)))
    (C D:I→MarkedCycleTuple tail head ktail khead (n+1) π b)
    (hC:∀ i a,(C i).val a=Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) (p i)) (ρ i a))
    (hD:∀ i a,(D i).val a=Fin.cons (α:=fun _=>V) (v' i) (Fin.cons (w' i) (p i)) (ρ i a))
    (R P:Finset V) (T:I→Finset V) (B:Finset U) (c:ℝ)
    (hroots:∀ i,v i∈R∧w i∈R∧v' i∈R∧w' i∈R)
    (hcross:∀ i,v i≠v' i∧v i≠w' i∧w i≠v' i∧w i≠w' i)
    (hP:∀ i a,p i a∈P) (hPR:Disjoint P R)
    (hPP:∀ x∈P,∀ y∈P,x≠y→¬PermutationClose π b x y)
    (hsepPR:∀ x∈P,∀ y∈R,¬PermutationClose π b x y)
    (hRR:∀ i,∀ x∈({v i,w i,v' i,w' i}:Finset V),
      ∀ y∈({v i,w i,v' i,w' i}:Finset V),x≠y→¬PermutationClose π b x y)
    (hTP:∀ i,T i⊆P) (hTcard:∀ i,(T i).card≤4)
    (hTex:∀ i,Disjoint (T i) (Finset.univ.image (C i).val∪Finset.univ.image (D i).val))
    (hcount:∀ A Q:Finset V,Disjoint A Q→A.card+Q.card≤n+8→
      (∀ x∈A∪Q,∀ y∈A∪Q,x≠y→¬PermutationClose π b x y)→
      c≤((Finset.univ.filter (fun u=>(∀ x∈A,H₀ x u)∧∀ x∈Q,HK x u)).card:ℝ))
    (hbudget:B.card+Fintype.card I<c):
    ∃ h:I↪U,∃ A D':I→MarkedWheel tail head ktail khead (n+1) π b H₀ HK,
      (∀ i,h i∉B)∧(∀ i,(A i).1=C i∧(D' i).1=D i∧(A i).2.val=h i∧(D' i).2.val=h i)∧
      ∀ i,∀ x∈T i,H₀ x (h i):=by
  let S₀:=fun i=>markedPairOrdinaryRows (C i) (D i) (T i)
  let SK:=fun i=>markedPairMarkedRows (C i) (D i)
  have hfree (i:I) (a:Fin n):p i a≠v i∧p i a≠w i∧p i a≠v' i∧p i a≠w' i:=by
    have hh:∀ x∈R,p i a≠x:=by
      intro x hx he
      exact Finset.disjoint_left.mp hPR (hP i a) (he ▸ hx)
    exact ⟨hh _ (hroots i).1,hh _ (hroots i).2.1,hh _ (hroots i).2.2.1,hh _ (hroots i).2.2.2⟩
  have halign (i:I):∀ a z,(C i).val a=(D i).val z→a=z:=by
    intro a z he
    rw [hC,hD] at he
    exact rotated_shared_two_root_path_alignment (p i) (p i).injective _ _ _ _ (ρ i) (hcross i) (hfree i) a z he
  have hT (i:I):∀ x∈T i,x≠(C i).val 0∧x≠(D i).val 0:=by
    intro x hx
    have hh:=Finset.disjoint_left.mp (hTex i) hx
    constructor
    · intro he;apply hh
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,he.symm⟩)
    · intro he;apply hh
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,he.symm⟩)
  have himage (i:I):(Finset.univ.image (C i).val∪Finset.univ.image (D i).val)=
      ({v i,w i,v' i,w' i}:Finset V)∪Finset.univ.image (p i):=by
    have hc:(C i).val=fun a=>Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) (p i)) (ρ i a):=funext (hC i)
    have hd:(D i).val=fun a=>Fin.cons (α:=fun _=>V) (v' i) (Fin.cons (w' i) (p i)) (ρ i a):=funext (hD i)
    rw [hc,hd,two_root_cycle_pair_image]
  have hsize (i:I):(S₀ i).card+(SK i).card≤n+8:=by
    have hc:(C i).val=fun a=>Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) (p i)) (ρ i a):=funext (hC i)
    have hd:(D i).val=fun a=>Fin.cons (α:=fun _=>V) (v' i) (Fin.cons (w' i) (p i)) (ρ i a):=funext (hD i)
    have hcard:(Finset.univ.image (C i).val∪Finset.univ.image (D i).val).card≤(n+1)+3:=by
      rw [hc,hd]
      exact two_root_cycle_pair_card (p i) _ _ _ _ (ρ i)
    exact marked_pair_hub_rows_card (C i) (D i) (T i) (halign i) (hT i) hcard (hTcard i)
  have hsep (i:I):∀ x∈S₀ i∪SK i,∀ y∈S₀ i∪SK i,x≠y→¬PermutationClose π b x y:=by
    let Rᵢ:Finset V:={v i,w i,v' i,w' i}
    have hRi:Rᵢ⊆R:=by
      intro x hx
      simp only [Rᵢ,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl
      · exact (hroots i).1
      · exact (hroots i).2.1
      · exact (hroots i).2.2.1
      · exact (hroots i).2.2.2
    have hs:S₀ i∪SK i⊆Rᵢ∪P:=by
      intro x hx
      have hh:=marked_pair_hub_rows_subset (C i) (D i) (T i) hx
      rcases Finset.mem_union.mp hh with hh|hh
      · rw [himage] at hh
        rcases Finset.mem_union.mp hh with hh|hh
        · exact Finset.mem_union_left _ hh
        · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hh
          exact Finset.mem_union_right _ (hP i a)
      · exact Finset.mem_union_right _ (hTP i hh)
    have hr:=permutationSeparated_union Rᵢ P (hRR i) hPP (fun x hx y hy hc=>
      hsepPR y hy x (hRi hx) ((permutationClose_symm π b x y).mp hc))
    exact fun x hx y hy hxy=>hr x (hs hx) y (hs hy) hxy
  obtain ⟨h,hB,hh⟩:=fresh_marked_transformer_hubs π b (n+8) H₀ HK S₀ SK B c
    (fun i=>marked_pair_hub_rows_disjoint (C i) (D i) (T i) (halign i) (hT i)) hsize hsep hcount hbudget
  have hw:∀ i,∃ A D':MarkedWheel tail head ktail khead (n+1) π b H₀ HK,
      A.1=C i∧D'.1=D i∧A.2.val=h i∧D'.2.val=h i:=by
    intro i
    have ht:=marked_pair_hub_rows_contain (C i) (D i) (T i)
    exact marked_cycle_pair_at_typed_hub H₀ HK (C i) (D i) (S₀ i) (SK i) (h i)
      ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 (hh i).1 (hh i).2
  choose A D' hAD using hw
  refine ⟨h,A,D',hB,hAD,?_⟩
  intro i x hx
  exact (hh i).1 x ((marked_pair_hub_rows_contain (C i) (D i) (T i)).2.2.2.2 hx)

end Oberwolfach
