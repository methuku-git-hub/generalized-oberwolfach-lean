module

public import Oberwolfach.MarkedPathPhysicalEdges
public import Oberwolfach.OrdinaryCycleRootCounts
public import Oberwolfach.PatternSurvivalMean

@[expose] public section

/-! The independent physical requests for each actual parent common path.
Its four root spokes are absent from this family of requests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (j : Bool) (T₀ TK : Finset V) (v v' : V)

abbrev DenseRootMarkedPathFamily := {z : Fin (m+1)→V // DenseRootMarkedPath P π b j T₀ TK v v' z}

theorem denseRootMarkedPath_free_separated (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') :
    PermutationSeparated π b C.val := by
  intro i k hik
  exact C.property.1 i.succ k.succ (fun h=>hik (Fin.succ_injective (m+1) h))

def markedPathRequiredEdges (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') : Finset (Sym2 V) :=
  Finset.univ.image (pathPhysicalEdge π j v v' C.val)

def pathPositionType (i : Fin m⊕(Bool×Bool)) : Bool :=
  match i with
  | Sum.inl i=>pathInternalType j i
  | Sum.inr (closing,_)=>if closing then j else false

def markedPathPositionState (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v')
    (i : Fin m⊕(Bool×Bool)) : Option (Bool×Bool) :=
  some (pathPositionType m j i,orientationBit (pathPhysicalTail v v' C.val i) (pathPhysicalHead π j v v' C.val i))

def markedPathRequiredState (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v')
    (e : Sym2 V) : Option (Bool×Bool) :=
  if h : ∃ i,pathPhysicalEdge π j v v' C.val i=e then
    markedPathPositionState P π b m j T₀ TK v v' C (Classical.choose h) else none

theorem markedPathRequiredState_apply (hb : 1≤b) (hm : 1≤m) (hvv' : v≠v')
    (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') (i : Fin m⊕(Bool×Bool)) :
    markedPathRequiredState P π b m j T₀ TK v v' C (pathPhysicalEdge π j v v' C.val i)=
      markedPathPositionState P π b m j T₀ TK v v' C i := by
  unfold markedPathRequiredState
  rw [dif_pos ⟨i,rfl⟩]
  congr 1
  exact pathPhysicalEdge_injective π b hb hm j v v' hvv' C.val
    (denseRootMarkedPath_free_separated P π b m j T₀ TK v v' C) C.property.1 C.property.2.1
    (Classical.choose_spec (show ∃ k,pathPhysicalEdge π j v v' C.val k=pathPhysicalEdge π j v v' C.val i from ⟨i,rfl⟩))

theorem markedPathRequiredEdges_card (hb : 1≤b) (hm : 1≤m) (hvv' : v≠v')
    (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') :
    (markedPathRequiredEdges P π b m j T₀ TK v v' C).card=m+4 := by
  rw [markedPathRequiredEdges,Finset.card_image_of_injective _
    (pathPhysicalEdge_injective π b hb hm j v v' hvv' C.val
      (denseRootMarkedPath_free_separated P π b m j T₀ TK v v' C) C.property.1 C.property.2.1)]
  simp

theorem markedPathRequiredEdges_label_in_range
    (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') (e : Sym2 V)
    (he : e∈markedPathRequiredEdges P π b m j T₀ TK v v' C) :
    e.out.1∈Set.range C.val ∨ e.out.2∈Set.range C.val := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
  have hout := e.out_eq
  have hinc : pathPhysicalTail v v' C.val i∈Set.range C.val ∨ pathPhysicalHead π j v v' C.val i∈Set.range C.val := by
    cases i with
    | inl i=>exact Or.inl ⟨i.castSucc,rfl⟩
    | inr i=>
      rcases i with ⟨closing,side⟩
      cases closing
      · exact Or.inr ⟨0,rfl⟩
      · exact Or.inl ⟨Fin.last m,rfl⟩
  change s(pathPhysicalTail v v' C.val i,pathPhysicalHead π j v v' C.val i)=e at hi
  have hpair : s(pathPhysicalTail v v' C.val i,pathPhysicalHead π j v v' C.val i)=s(e.out.1,e.out.2) := hi.trans hout.symm
  rcases Sym2.eq_iff.mp hpair with ⟨ht,hh⟩|⟨ht,hh⟩
  · rcases hinc with ⟨a,ha⟩|⟨a,ha⟩
    · exact Or.inl ⟨a,ha.trans ht⟩
    · exact Or.inr ⟨a,ha.trans hh⟩
  · rcases hinc with ⟨a,ha⟩|⟨a,ha⟩
    · exact Or.inr ⟨a,ha.trans ht⟩
    · exact Or.inl ⟨a,ha.trans hh⟩

theorem markedPath_edge_incidence (e : Sym2 V) :
    (∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',
      if e∈markedPathRequiredEdges P π b m j T₀ TK v v' C then (1:ℝ) else 0)≤
        2*((m:ℝ)+1)*(Fintype.card V:ℝ)^m := by
  let g := fun (x : V) (f : Fin (m+1)→V)=>if x∈Set.range f then (1:ℝ) else 0
  have hbound (x : V) : (∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',g x C.val)≤
      ((m:ℝ)+1)*(Fintype.card V:ℝ)^m := by
    have hh := finite_subtype_sum_le (DenseRootMarkedPath P π b j T₀ TK v v') (g x)
      (by intro f;dsimp [g];split_ifs <;> norm_num)
    have hc := functions_cover_roots_count (0 : Fin (m+1)) ({x}:Finset V)
    simp only [Finset.mem_singleton,forall_eq,Finset.card_singleton,Fintype.card_fin,
      Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_one] at hc
    exact hh.trans hc
  have hp (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') :
      (if e∈markedPathRequiredEdges P π b m j T₀ TK v v' C then (1:ℝ) else 0)≤g e.out.1 C.val+g e.out.2 C.val := by
    by_cases he : e∈markedPathRequiredEdges P π b m j T₀ TK v v' C
    · obtain h|h := markedPathRequiredEdges_label_in_range P π b m j T₀ TK v v' C e he
      · simp only [he,ite_true,g,h,ite_true];split_ifs <;> norm_num
      · simp only [he,ite_true,g,h,ite_true];split_ifs <;> norm_num
    · simp only [he,ite_false,g];split_ifs <;> norm_num
  have hh := Finset.sum_le_sum (fun C (_ : C∈Finset.univ)=>hp C)
  rw [Finset.sum_add_distrib] at hh
  linarith only [hh,hbound e.out.1,hbound e.out.2]

theorem markedPathRequiredState_mass_lower (hb : 1≤b) (hm : 1≤m) (hvv' : v≠v')
    (p k pstar : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (hplo : pstar≤p) (hklo : pstar≤k)
    (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') (e : Sym2 V)
    (he : e∈markedPathRequiredEdges P π b m j T₀ TK v v' C) :
    pstar≤(markedPhysicalLaw p k hp hk hsum).mass (markedPathRequiredState P π b m j T₀ TK v v' C e) := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  rw [markedPathRequiredState_apply P π b m j T₀ TK v v' hb hm hvv']
  change pstar≤ if pathPositionType m j i then k else p
  split_ifs <;> assumption

end Oberwolfach
