module

public import Oberwolfach.MarkedBaseCycleCounts
public import Oberwolfach.MarkedPhysicalLaw
public import Oberwolfach.OrdinaryCycleRootCounts
public import Oberwolfach.PatternSurvivalMean

@[expose] public section

/-! Physical state requirements for actual marked base cycles. The lookup
uses the injective physical-edge map; ordinary and marked requirements are
never sampled as independent occurrences of the same underlying edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (T₀ TK : Finset V)

abbrev DenseMarkedBaseFamily := {f : Fin (m+1)→V // DenseMarkedBase P π b T₀ TK f}

def markedBaseRequiredEdges (C : DenseMarkedBaseFamily P π b m T₀ TK) : Finset (Sym2 V) :=
  Finset.univ.image (twistedTupleEdge C.val (π (C.val 0)))

def markedBasePositionState (C : DenseMarkedBaseFamily P π b m T₀ TK) :
    Fin m⊕Unit→Option (Bool×Bool)
  | Sum.inl i=>some (false,orientationBit (C.val i.castSucc) (C.val i.succ))
  | Sum.inr _=>some (true,orientationBit (C.val (Fin.last m)) (π (C.val 0)))

def markedBaseRequiredState (C : DenseMarkedBaseFamily P π b m T₀ TK)
    (e : Sym2 V) : Option (Bool×Bool) :=
  if h : ∃ i,twistedTupleEdge C.val (π (C.val 0)) i=e then
    markedBasePositionState P π b m T₀ TK C (Classical.choose h) else none

theorem markedBaseRequiredState_apply (hb : 1≤b) (hm : 2≤m)
    (C : DenseMarkedBaseFamily P π b m T₀ TK) (i : Fin m⊕Unit) :
    markedBaseRequiredState P π b m T₀ TK C (twistedTupleEdge C.val (π (C.val 0)) i)=
      markedBasePositionState P π b m T₀ TK C i := by
  unfold markedBaseRequiredState
  rw [dif_pos ⟨i,rfl⟩]
  congr 1
  exact denseMarkedBase_physical_injective P π b m hb hm T₀ TK C.val C.property
    (Classical.choose_spec (show ∃ j,twistedTupleEdge C.val (π (C.val 0)) j=
      twistedTupleEdge C.val (π (C.val 0)) i from ⟨i,rfl⟩))

theorem markedBaseRequiredEdges_card (hb : 1≤b) (hm : 2≤m)
    (C : DenseMarkedBaseFamily P π b m T₀ TK) : (markedBaseRequiredEdges P π b m T₀ TK C).card=m+1 := by
  rw [markedBaseRequiredEdges,Finset.card_image_of_injective _
    (denseMarkedBase_physical_injective P π b m hb hm T₀ TK C.val C.property)]
  simp

theorem markedBaseRequiredEdges_tail_in_range
    (C : DenseMarkedBaseFamily P π b m T₀ TK) (e : Sym2 V)
    (he : e∈markedBaseRequiredEdges P π b m T₀ TK C) :
    e.out.1∈Set.range C.val ∨ e.out.2∈Set.range C.val := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
  have hout := e.out_eq
  cases i with
  | inl i=>
    change s(C.val i.castSucc,C.val i.succ)=e at hi
    rw [← hout] at hi
    rcases Sym2.eq_iff.mp hi with ⟨hx,hy⟩|⟨hx,hy⟩
    · exact Or.inl ⟨i.castSucc,hx⟩
    · exact Or.inr ⟨i.castSucc,hx⟩
  | inr i=>
    change s(C.val (Fin.last m),π (C.val 0))=e at hi
    rw [← hout] at hi
    rcases Sym2.eq_iff.mp hi with ⟨hx,hy⟩|⟨hx,hy⟩
    · exact Or.inl ⟨Fin.last m,hx⟩
    · exact Or.inr ⟨Fin.last m,hx⟩

theorem markedBase_edge_incidence (e : Sym2 V) :
    (∑ C : DenseMarkedBaseFamily P π b m T₀ TK,
      if e∈markedBaseRequiredEdges P π b m T₀ TK C then (1:ℝ) else 0)≤
        2*((m:ℝ)+1)*(Fintype.card V:ℝ)^m := by
  let g := fun (x : V) (f : Fin (m+1)→V)=>if x∈Set.range f then (1:ℝ) else 0
  have hbound (x : V) : (∑ C : DenseMarkedBaseFamily P π b m T₀ TK,g x C.val)≤
      ((m:ℝ)+1)*(Fintype.card V:ℝ)^m := by
    have hh := finite_subtype_sum_le (DenseMarkedBase P π b T₀ TK) (g x)
      (by intro f;dsimp [g];split_ifs <;> norm_num)
    have hc := functions_cover_roots_count (0 : Fin (m+1)) ({x}:Finset V)
    simp only [Finset.mem_singleton,forall_eq,Finset.card_singleton,Fintype.card_fin,
      Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_one] at hc
    exact hh.trans hc
  have hp (C : DenseMarkedBaseFamily P π b m T₀ TK) :
      (if e∈markedBaseRequiredEdges P π b m T₀ TK C then (1:ℝ) else 0)≤g e.out.1 C.val+g e.out.2 C.val := by
    by_cases he : e∈markedBaseRequiredEdges P π b m T₀ TK C
    · obtain h|h := markedBaseRequiredEdges_tail_in_range P π b m T₀ TK C e he
      · simp only [he,ite_true,g,h,ite_true];split_ifs <;> norm_num
      · simp only [he,ite_true,g,h,ite_true];split_ifs <;> norm_num
    · simp only [he,ite_false,g];split_ifs <;> norm_num
  have hh := Finset.sum_le_sum (fun C (_ : C∈Finset.univ)=>hp C)
  rw [Finset.sum_add_distrib] at hh
  linarith only [hh,hbound e.out.1,hbound e.out.2]

theorem markedBaseRequiredState_mass_lower (hb : 1≤b) (hm : 2≤m)
    (p k pstar : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (hplo : pstar≤p) (hklo : pstar≤k)
    (C : DenseMarkedBaseFamily P π b m T₀ TK) (e : Sym2 V)
    (he : e∈markedBaseRequiredEdges P π b m T₀ TK C) :
    pstar≤(markedPhysicalLaw p k hp hk hsum).mass (markedBaseRequiredState P π b m T₀ TK C e) := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  rw [markedBaseRequiredState_apply P π b m T₀ TK hb hm]
  cases i
  · exact hplo
  · exact hklo

end Oberwolfach
