module

public import Oberwolfach.FixedDomainTupleChanges
public import Oberwolfach.MarkedBaseRealization
public import Oberwolfach.MarkedPathRealization

@[expose] public section

/-! Actual local cycle/path families under changes of their spoke classes.
Every free coordinate lies in the fixed inner set A. The two path roots
remain fixed and need not lie in A; no root-spoke condition is inserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedLocalBase_class_loss (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ)
    (A T₀ TK T₀' TK' : Finset V) (hT₀ : T₀⊆A) (hTK : TK⊆A)
    (hT₀' : T₀'⊆A) (hTK' : TK'⊆A) (δ : ℝ)
    (hD₀ : ((T₀\T₀').card:ℝ)≤δ) (hDK : ((TK\TK').card:ℝ)≤δ)
    (σ : Sym2 V→Option (Bool×Bool)) :
    (Fintype.card {C : DenseMarkedBaseFamily P π b m T₀ TK // MarkedBaseRims P π b m σ C.val}:ℝ)-
      Fintype.card {C : DenseMarkedBaseFamily P π b m T₀' TK' // MarkedBaseRims P π b m σ C.val}≤
      ((m:ℝ)+1)*δ*(A.card:ℝ)^m := by
  have hc (S₀ SK : Finset V) :
      Fintype.card {C : DenseMarkedBaseFamily P π b m S₀ SK // MarkedBaseRims P π b m σ C.val}=
      Fintype.card {f : Fin (m+1)→V // DenseMarkedBase P π b S₀ SK f ∧ MarkedBaseRims P π b m σ f} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  rw [hc,hc]
  let P₀ := fun f : Fin (m+1)→V=>DenseMarkedBase P π b T₀ TK f ∧ MarkedBaseRims P π b m σ f
  let P₁ := fun f : Fin (m+1)→V=>DenseMarkedBase P π b T₀' TK' f ∧ MarkedBaseRims P π b m σ f
  let D := fun i : Fin (m+1)=>if i=0 then TK\TK' else T₀\T₀'
  have h0 : ∀ f,P₀ f → ∀ i,f i∈A := by
    intro f hf i
    exact Fin.cases (hTK hf.1.2.1) (fun i=>hT₀ (hf.1.2.2.1 i)) i
  have h1 : ∀ f,P₁ f → ∀ i,f i∈A := by
    intro f hf i
    exact Fin.cases (hTK' hf.1.2.1) (fun i=>hT₀' (hf.1.2.2.1 i)) i
  have hD : ∀ i,((D i).card:ℝ)≤δ := by intro i;dsimp [D];split_ifs <;> assumption
  have hbad : ∀ f,P₀ f → ¬P₁ f → ∃ i,f i∈D i := by
    intro f hf hn
    by_contra hnone
    have hk : f 0∈TK' := by
      by_contra hnot
      apply hnone
      exact ⟨0,by simpa only [D,ite_true,Finset.mem_sdiff] using And.intro hf.1.2.1 hnot⟩
    have ho : ∀ i : Fin m,f i.succ∈T₀' := by
      intro i
      by_contra hnot
      apply hnone
      exact ⟨i.succ,by simpa only [D,Fin.succ_ne_zero,ite_false,Finset.mem_sdiff] using And.intro (hf.1.2.2.1 i) hnot⟩
    exact hn ⟨⟨hf.1.1,hk,ho,hf.1.2.2.2⟩,hf.2⟩
  have hh := fixedDomainTuple_predicate_loss A P₀ P₁ h0 h1 D δ hD hbad
  simp only [P₀,P₁,Fintype.card_fin,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] at hh
  simpa only [Fintype.card_eq_nat_card] using hh

theorem markedLocalPath_class_loss (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ)
    (j : Bool) (v v' : V) (A T₀ TK T₀' TK' : Finset V) (hT₀ : T₀⊆A) (hTK : TK⊆A)
    (hT₀' : T₀'⊆A) (hTK' : TK'⊆A) (δ : ℝ)
    (hD₀ : ((T₀\T₀').card:ℝ)≤δ) (hDK : ((TK\TK').card:ℝ)≤δ)
    (σ : Sym2 V→Option (Bool×Bool)) :
    (Fintype.card {C : DenseRootMarkedPathFamily P π b m j T₀ TK v v' // MarkedPathRims P π b m j v v' σ C.val}:ℝ)-
      Fintype.card {C : DenseRootMarkedPathFamily P π b m j T₀' TK' v v' // MarkedPathRims P π b m j v v' σ C.val}≤
      ((m:ℝ)+1)*δ*(A.card:ℝ)^m := by
  have hc (S₀ SK : Finset V) :
      Fintype.card {C : DenseRootMarkedPathFamily P π b m j S₀ SK v v' // MarkedPathRims P π b m j v v' σ C.val}=
      Fintype.card {f : Fin (m+1)→V // DenseRootMarkedPath P π b j S₀ SK v v' f ∧ MarkedPathRims P π b m j v v' σ f} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  rw [hc,hc]
  let P₀ := fun f : Fin (m+1)→V=>DenseRootMarkedPath P π b j T₀ TK v v' f ∧ MarkedPathRims P π b m j v v' σ f
  let P₁ := fun f : Fin (m+1)→V=>DenseRootMarkedPath P π b j T₀' TK' v v' f ∧ MarkedPathRims P π b m j v v' σ f
  let D := fun i : Fin (m+1)=>if j=false ∧ i.val=2 then TK\TK' else T₀\T₀'
  have h0 : ∀ f,P₀ f → ∀ i,f i∈A := by
    intro f hf i
    have hi := hf.1.2.2.1 i
    split_ifs at hi
    · exact hTK hi
    · exact hT₀ hi
  have h1 : ∀ f,P₁ f → ∀ i,f i∈A := by
    intro f hf i
    have hi := hf.1.2.2.1 i
    split_ifs at hi
    · exact hTK' hi
    · exact hT₀' hi
  have hD : ∀ i,((D i).card:ℝ)≤δ := by intro i;dsimp [D];split_ifs <;> assumption
  have hbad : ∀ f,P₀ f → ¬P₁ f → ∃ i,f i∈D i := by
    intro f hf hn
    by_contra hnone
    have hs : ∀ i,f i∈if j=false ∧ i.val=2 then TK' else T₀' := by
      intro i
      have hi := hf.1.2.2.1 i
      by_contra hnot
      apply hnone
      refine ⟨i,?_⟩
      dsimp only [D]
      split_ifs at hi hnot ⊢ <;> exact Finset.mem_sdiff.mpr ⟨hi,hnot⟩
    exact hn ⟨⟨hf.1.1,hf.1.2.1,hs,hf.1.2.2.2⟩,hf.2⟩
  have hh := fixedDomainTuple_predicate_loss A P₀ P₁ h0 h1 D δ hD hbad
  simp only [P₀,P₁,Fintype.card_fin,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] at hh
  simpa only [Fintype.card_eq_nat_card] using hh

end Oberwolfach
