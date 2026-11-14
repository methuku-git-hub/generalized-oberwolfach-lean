module

public import Oberwolfach.MarkedFiniteBalanceValues

@[expose] public section

/-! Balance restricted only at the opposite endpoint. All roots remain
ambient. Difference of nested row/hub domains gives an exact subtraction
identity; physical edge deletion likewise subtracts its actual incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_filter_domain_sdiff {A B:Type} [DecidableEq A] [DecidableEq B]
    (S:Finset A) (f:A→B) (X T:Finset B):
    S.filter (fun a=>f a∈X\T)=S.filter (fun a=>f a∈X)\S.filter (fun a=>f a∈T):=by
  ext a
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  tauto

theorem finite_filter_set_sdiff {A:Type} [DecidableEq A] (S T:Finset A) (p:A→Prop) [DecidablePred p]:
    (S\T).filter p=S.filter p\T.filter p:=by
  ext a
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  tauto

variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def markedFiniteDomainBalance (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (X:Finset V) (Z:Finset U):V⊕U→Fin 4→ℝ
  | Sum.inl v=>markedFiniteBalance tail head ktail khead HK
      (A.filter (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈X))
      (S.filter (fun s=>s.2∈Z)) m (Sum.inl v)
  | Sum.inr u=>markedFiniteBalance tail head ktail khead HK ∅ (S.filter (fun s=>s.1∈X)) m (Sum.inr u)

theorem markedFiniteDomainBalance_domain_sdiff
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (X T:Finset V) (Z W:Finset U)
    (hT:T⊆X) (hW:W⊆Z) (z:V⊕U) (i:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK A S m (X\T) (Z\W) z i=
      markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i-
      markedFiniteDomainBalance tail head ktail khead HK A S m T W z i:=by
  cases z with
  | inl v=>
    dsimp only [markedFiniteDomainBalance]
    rw [finite_filter_domain_sdiff,finite_filter_domain_sdiff]
    apply markedFiniteBalance_sdiff
    · intro a ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,hT (Finset.mem_filter.mp ha).2⟩
    · intro s hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1,hW (Finset.mem_filter.mp hs).2⟩
  | inr u=>
    dsimp only [markedFiniteDomainBalance]
    rw [finite_filter_domain_sdiff]
    have hh:=markedFiniteBalance_sdiff tail head ktail khead HK ∅ ∅
      (S.filter (fun s=>s.1∈X)) (S.filter (fun s=>s.1∈T)) m (Finset.Subset.refl _) (by
        intro s hs
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1,hT (Finset.mem_filter.mp hs).2⟩) (Sum.inr u) i
    simpa only [Finset.empty_sdiff] using hh

theorem markedFiniteDomainBalance_sdiff
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A B:Finset (E⊕K)) (S R:Finset (V×U)) (m:ℕ) (X:Finset V) (Z:Finset U)
    (hA:B⊆A) (hS:R⊆S) (z:V⊕U) (i:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK (A\B) (S\R) m X Z z i=
      markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i-
      markedFiniteDomainBalance tail head ktail khead HK B R m X Z z i:=by
  cases z with
  | inl v=>
    dsimp only [markedFiniteDomainBalance]
    rw [finite_filter_set_sdiff,finite_filter_set_sdiff]
    exact markedFiniteBalance_sdiff _ _ _ _ _ _ _ _ _ _
      (Finset.filter_subset_filter _ hA) (Finset.filter_subset_filter _ hS) _ i
  | inr u=>
    dsimp only [markedFiniteDomainBalance]
    rw [finite_filter_set_sdiff]
    have hh:=markedFiniteBalance_sdiff tail head ktail khead HK ∅ ∅
      (S.filter (fun s=>s.1∈X)) (R.filter (fun s=>s.1∈X)) m (Finset.Subset.refl _)
      (Finset.filter_subset_filter _ hS) (Sum.inr u) i
    simpa only [Finset.empty_sdiff] using hh

end Oberwolfach
