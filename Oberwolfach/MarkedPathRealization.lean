module

public import Oberwolfach.MarkedPathSurvival
public import Oberwolfach.MarkedSampleArcs

@[expose] public section

/-! Each physical pattern is exactly the two rooted cycles' actual sampled
rim requirements. Their four root spokes are still omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (j : Bool) (T₀ TK : Finset V) (v v' : V)

def pathAuxiliaryHead (z : Fin (m+1)→V) : Fin m⊕(Bool×Bool)→V
  | Sum.inl i=>z i.succ
  | Sum.inr (closing,side)=>if closing then (if side then v' else v) else z 0

theorem pathPhysicalHead_auxiliary (z : Fin (m+1)→V) (i : Fin m⊕(Bool×Bool)) :
    pathPhysicalHead π j v v' z i=optionalSuccessor π (pathPositionType m j i) (pathAuxiliaryHead m v v' z i) := by
  cases i with
  | inl i=>rfl
  | inr i=>rcases i with ⟨closing,side⟩;cases closing <;> rfl

def MarkedPathRims (σ : Sym2 V→Option (Bool×Bool)) (z : Fin (m+1)→V) : Prop :=
  ∀ i : Fin m⊕(Bool×Bool),markedPhysicalRim P π b σ (pathPositionType m j i)
    (pathPhysicalTail v v' z i) (pathAuxiliaryHead m v v' z i)=1

theorem denseRootMarkedPath_physical_adj
    (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') (i : Fin m⊕(Bool×Bool)) :
    P.Adj (pathPhysicalTail v v' C.val i) (pathPhysicalHead π j v v' C.val i) := by
  rcases C.property with ⟨_,_,_,hopen,hopen',hclose,hclose',hpath⟩
  cases i with
  | inl i=>simpa only [pathPhysicalTail,pathPhysicalHead,optionalSuccessor,pathInternalType,decide_eq_true_eq] using hpath i
  | inr i=>
    rcases i with ⟨closing,side⟩
    cases closing <;> cases side
    · exact hopen
    · exact hopen'
    · exact hclose
    · exact hclose'

theorem denseRootMarkedPath_auxiliary_separated (hm : 1≤m)
    (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') (i : Fin m⊕(Bool×Bool)) :
    ¬PermutationClose π b (pathPhysicalTail v v' C.val i) (pathAuxiliaryHead m v v' C.val i) := by
  cases i with
  | inl i=>
    apply denseRootMarkedPath_free_separated P π b m j T₀ TK v v' C i.castSucc i.succ
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  | inr i=>
    rcases i with ⟨closing,side⟩
    have hsep : PermutationSeparated π b (Fin.cons (if side then v' else v) C.val) := by
      cases side
      · exact C.property.1
      · exact C.property.2.1
    cases closing
    · exact hsep 0 (0:Fin (m+1)).succ (Ne.symm (Fin.succ_ne_zero _))
    · exact hsep (Fin.last m).succ 0 (Fin.succ_ne_zero _)

theorem markedPath_states_iff_rims (hb : 1≤b) (hm : 1≤m) (hvv' : v≠v')
    (C : DenseRootMarkedPathFamily P π b m j T₀ TK v v') (σ : Sym2 V→Option (Bool×Bool)) :
    (∀ e∈markedPathRequiredEdges P π b m j T₀ TK v v' C,
      σ e=markedPathRequiredState P π b m j T₀ TK v v' C e) ↔ MarkedPathRims P π b m j v v' σ C.val := by
  have hstates : (∀ e∈markedPathRequiredEdges P π b m j T₀ TK v v' C,
      σ e=markedPathRequiredState P π b m j T₀ TK v v' C e) ↔
      ∀ i : Fin m⊕(Bool×Bool),σ (pathPhysicalEdge π j v v' C.val i)=
        markedPathPositionState P π b m j T₀ TK v v' C i := by
    constructor
    · intro h i
      have hh := h _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simpa only [markedPathRequiredState_apply P π b m j T₀ TK v v' hb hm hvv'] using hh
    · intro h e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      rw [markedPathRequiredState_apply P π b m j T₀ TK v v' hb hm hvv']
      exact h i
  rw [hstates]
  unfold MarkedPathRims
  apply forall_congr'
  intro i
  rw [markedPhysicalRim_eq_one_iff]
  have hsep := denseRootMarkedPath_auxiliary_separated P π b m j T₀ TK v v' hm C i
  have hAdj := denseRootMarkedPath_physical_adj P π b m j T₀ TK v v' C i
  have he := pathPhysicalHead_auxiliary π m j v v' C.val i
  change pathPhysicalHead π j v v' C.val i=
    (if pathPositionType m j i then π (pathAuxiliaryHead m v v' C.val i) else pathAuxiliaryHead m v v' C.val i) at he
  simp only [← he,hsep,hAdj,not_false_eq_true,true_and,pathPhysicalEdge,markedPathPositionState]

theorem markedPathSurvivalSum_count (hb : 1≤b) (hm : 1≤m) (hvv' : v≠v')
    (σ : Sym2 V→Option (Bool×Bool)) :
    markedPathSurvivalSum P π b m j T₀ TK v v' σ=
      (Fintype.card {C : DenseRootMarkedPathFamily P π b m j T₀ TK v v' //
        MarkedPathRims P π b m j v v' σ C.val}:ℝ)/(Fintype.card V:ℝ)^(m+1) := by
  unfold markedPathSurvivalSum
  simp_rw [patternValue_indicator,markedPath_states_iff_rims P π b m j T₀ TK v v' hb hm hvv']
  rw [← Finset.mul_sum]
  have hcard : (∑ C : DenseRootMarkedPathFamily P π b m j T₀ TK v v',
      if MarkedPathRims P π b m j v v' σ C.val then (1:ℝ) else 0)=
      Fintype.card {C : DenseRootMarkedPathFamily P π b m j T₀ TK v v' //
        MarkedPathRims P π b m j v v' σ C.val} := by
    simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hcard]
  ring

end Oberwolfach
