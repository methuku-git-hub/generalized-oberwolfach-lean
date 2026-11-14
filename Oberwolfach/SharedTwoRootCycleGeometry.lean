module

public import Oberwolfach.SharedPathIndexAlignment
public import Oberwolfach.MarkedCycleRotation

@[expose] public section

/-! Vertex sets and index alignment of the two cycles obtained by changing
only the two old endpoints of a shared path. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V] {n:ℕ}

 theorem two_root_cycle_image (p:Fin n→V) (v w:V) (ρ:Equiv.Perm (Fin (n+2))):
    Finset.univ.image (fun i=>Fin.cons (α:=fun _=>V) v (Fin.cons w p) (ρ i))=
      insert v (insert w (Finset.univ.image p)):=by
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    have hh:∀ j:Fin (n+2),Fin.cons (α:=fun _=>V) v (Fin.cons w p) j=x→
        x=v∨x=w∨∃ k,p k=x:=by
      intro j
      refine Fin.cases ?_ (fun j=>?_) j
      · intro h;exact Or.inl h.symm
      · refine Fin.cases ?_ (fun j=>?_) j
        · intro h;exact Or.inr (Or.inl h.symm)
        · intro h;exact Or.inr (Or.inr ⟨j,h⟩)
    exact hh (ρ i) hi
  · rintro (rfl|rfl|⟨i,hi⟩)
    · exact ⟨ρ.symm 0,by simp⟩
    · exact ⟨ρ.symm (0:Fin (n+1)).succ,by simp⟩
    · exact ⟨ρ.symm i.succ.succ,by simpa using hi⟩

 theorem two_root_cycle_pair_image (p:Fin n→V) (v w v' w':V) (ρ:Equiv.Perm (Fin (n+2))):
    (Finset.univ.image (fun i=>Fin.cons (α:=fun _=>V) v (Fin.cons w p) (ρ i)))∪
      (Finset.univ.image (fun i=>Fin.cons (α:=fun _=>V) v' (Fin.cons w' p) (ρ i)))=
      ({v,w,v',w'}:Finset V)∪Finset.univ.image p:=by
  rw [two_root_cycle_image,two_root_cycle_image]
  ext x
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto

 theorem two_root_cycle_pair_card (p:Fin n→V) (v w v' w':V) (ρ:Equiv.Perm (Fin (n+2))):
    ((Finset.univ.image (fun i=>Fin.cons (α:=fun _=>V) v (Fin.cons w p) (ρ i)))∪
      (Finset.univ.image (fun i=>Fin.cons (α:=fun _=>V) v' (Fin.cons w' p) (ρ i)))).card≤n+4:=by
  rw [two_root_cycle_pair_image]
  have h₁:({v,w,v',w'}:Finset V).card≤4:=by
    have ha:=Finset.card_insert_le v (insert w (insert v' ({w'}:Finset V)))
    have hb:=Finset.card_insert_le w (insert v' ({w'}:Finset V))
    have hc:=Finset.card_insert_le v' ({w'}:Finset V)
    have hd:({w'}:Finset V).card=1:=Finset.card_singleton _
    omega
  have h₂:(Finset.univ.image p).card≤n:=by
    simpa using Finset.card_image_le (f:=p) (s:=Finset.univ)
  have h₃:=Finset.card_union_le ({v,w,v',w'}:Finset V) (Finset.univ.image p)
  omega

 theorem rotated_shared_two_root_path_alignment (p:Fin n→V) (hp:Function.Injective p)
    (v w v' w':V) (ρ:Equiv.Perm (Fin (n+2)))
    (hcross:v≠v'∧v≠w'∧w≠v'∧w≠w')
    (hfree:∀ i,p i≠v∧p i≠w∧p i≠v'∧p i≠w'):
    ∀ i j,Fin.cons (α:=fun _=>V) v (Fin.cons w p) (ρ i)=
      Fin.cons (α:=fun _=>V) v' (Fin.cons w' p) (ρ j)→i=j:=by
  intro i j h
  exact ρ.injective (shared_two_root_path_index_alignment p hp v w v' w' hcross hfree _ _ h)

 theorem permutationSeparated_union {π:Equiv.Perm V} {b:ℕ} (A B:Finset V)
    (hA:∀ x∈A,∀ y∈A,x≠y→¬PermutationClose π b x y)
    (hB:∀ x∈B,∀ y∈B,x≠y→¬PermutationClose π b x y)
    (hcross:∀ x∈A,∀ y∈B,¬PermutationClose π b x y):
    ∀ x∈A∪B,∀ y∈A∪B,x≠y→¬PermutationClose π b x y:=by
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
  · exact hA x hx y hy hxy
  · exact hcross x hx y hy
  · exact fun hc=>hcross y hy x hx ((permutationClose_symm π b x y).mp hc)
  · exact hB x hx y hy hxy

end Oberwolfach
