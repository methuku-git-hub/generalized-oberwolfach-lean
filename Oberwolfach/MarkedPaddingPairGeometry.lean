module

public import Oberwolfach.MarkedPaddingPairConstruction

@[expose] public section

/-! Row sets of the two actual padding families. Old vertices need not be
separated within either side; only the paired roots need separation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype I] [DecidableEq V]
    {m b:ℕ} {π:Equiv.Perm V}

def pairedPaddingPrivateRows (p:Bool×I→(Fin m↪V)) (j:Bool):Finset V:=
  Finset.univ.biUnion (fun i:I=>Finset.univ.image (p (j,i)))

theorem paired_padding_private_rows_card (p:Bool×I→(Fin m↪V)) (j:Bool):
    (pairedPaddingPrivateRows p j).card≤Fintype.card I*m:=by
  calc
    _≤∑ i:I,(Finset.univ.image (p (j,i))).card:=Finset.card_biUnion_le
    _=Fintype.card I*m:=by simp [Finset.card_image_of_injective _ (p _).injective]

theorem paired_padding_root_sets (p:Bool×I→(Fin m↪V)) (R R':Finset V)
    (hRR:Disjoint R R')
    (hav:∀ i k,p i k∉R∪R')
    (hdis:∀ i j,i≠j→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p j))):
    Disjoint (R∪pairedPaddingPrivateRows p false) (R'∪pairedPaddingPrivateRows p true)∧
    ((R∪pairedPaddingPrivateRows p false)∪(R'∪pairedPaddingPrivateRows p true)).card≤
      (R∪R').card+2*Fintype.card I*m:=by
  have hz (j:Bool):Disjoint (pairedPaddingPrivateRows p j) (R∪R'):=by
    apply Finset.disjoint_left.mpr
    intro v hv hvZ
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hi
    exact hav (j,i) k hvZ
  have hp:Disjoint (pairedPaddingPrivateRows p false) (pairedPaddingPrivateRows p true):=by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hv'
    exact Finset.disjoint_left.mp (hdis (false,i) (true,j) (by simp)) hi hj
  refine ⟨Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hRR,(hz true).symm.mono_left Finset.subset_union_left⟩,
    Finset.disjoint_union_right.mpr ⟨(hz false).mono_right Finset.subset_union_right,hp⟩⟩,?_⟩
  have he:(R∪pairedPaddingPrivateRows p false)∪(R'∪pairedPaddingPrivateRows p true)=
      (R∪R')∪(pairedPaddingPrivateRows p false∪pairedPaddingPrivateRows p true):=by
    ext v;simp only [Finset.mem_union];tauto
  rw [he]
  have h₁:=Finset.card_union_le (R∪R') (pairedPaddingPrivateRows p false∪pairedPaddingPrivateRows p true)
  have h₂:=Finset.card_union_le (pairedPaddingPrivateRows p false) (pairedPaddingPrivateRows p true)
  have h₃:=paired_padding_private_rows_card p false
  have h₄:=paired_padding_private_rows_card p true
  rw [Nat.mul_assoc]
  omega

theorem paired_padding_cycle_row_mem (p:Bool×I→(Fin m↪V)) (v v':I→V) (R R':Finset V)
    (hv:∀ i,v i∈R∧v' i∈R') (j:Bool) (i:I) (k:Fin (m+1)):
    Fin.cons (α:=fun _=>V) (if j then v' i else v i) (p (j,i)) k∈
      (if j then R' else R)∪pairedPaddingPrivateRows p j:=by
  refine Fin.cases ?_ (fun q=>?_) k
  · simp only [Fin.cons_zero]
    apply Finset.mem_union_left
    cases j
    · exact (hv i).1
    · exact (hv i).2
  · simp only [Fin.cons_succ]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩⟩)

theorem paired_padding_cycle_row_cases (p:Bool×I→(Fin m↪V)) (v v':I→V)
    (j:Bool) (i:I) (k:Fin (m+1)):
    Fin.cons (α:=fun _=>V) (if j then v' i else v i) (p (j,i)) k=v i∨
    Fin.cons (α:=fun _=>V) (if j then v' i else v i) (p (j,i)) k=v' i∨
    ∃ q:Fin m,Fin.cons (α:=fun _=>V) (if j then v' i else v i) (p (j,i)) k=p (j,i) q:=by
  refine Fin.cases ?_ (fun q=>?_) k
  · cases j <;> simp
  · exact Or.inr (Or.inr ⟨q,rfl⟩)

theorem paired_padding_cycle_rows_separated (p:Bool×I→(Fin m↪V)) (v v':I→V) (Z:Finset V)
    (hv:∀ i,v i∈Z∧v' i∈Z)
    (hpair:∀ i,¬PermutationClose π b (v i) (v' i))
    (hav:∀ i k,∀ z∈Z,¬PermutationClose π b (p i k) z)
    (hsep:∀ i j,∀ k k',p i k≠p j k'→¬PermutationClose π b (p i k) (p j k')):
    ∀ i:I,∀ j j':Bool,∀ k k':Fin (m+1),
    Fin.cons (α:=fun _=>V) (if j then v' i else v i) (p (j,i)) k≠
      Fin.cons (α:=fun _=>V) (if j' then v' i else v i) (p (j',i)) k'→
    ¬PermutationClose π b
      (Fin.cons (α:=fun _=>V) (if j then v' i else v i) (p (j,i)) k)
      (Fin.cons (α:=fun _=>V) (if j' then v' i else v i) (p (j',i)) k'):=by
  intro i j j' k k' hne
  rcases paired_padding_cycle_row_cases p v v' j i k with hx|hx|⟨q,hx⟩ <;>
    rcases paired_padding_cycle_row_cases p v v' j' i k' with hy|hy|⟨q',hy⟩ <;>
    rw [hx,hy] at hne ⊢
  · exact False.elim (hne rfl)
  · exact hpair i
  · intro hc;exact hav (j',i) q' (v i) (hv i).1 ((permutationClose_symm π b _ _).mp hc)
  · intro hc;exact hpair i ((permutationClose_symm π b _ _).mp hc)
  · exact False.elim (hne rfl)
  · intro hc;exact hav (j',i) q' (v' i) (hv i).2 ((permutationClose_symm π b _ _).mp hc)
  · exact hav (j,i) q (v i) (hv i).1
  · exact hav (j,i) q (v' i) (hv i).2
  · exact hsep (j,i) (j',i) q q' hne

end Oberwolfach
