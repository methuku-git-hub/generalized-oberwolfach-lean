module

public import Oberwolfach.OrdinaryProtectedBoundaryHistoryEdit

@[expose] public section
/-! Sequential physical deletions, with a precise cumulative history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryDeletionHistory (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop):ℕ→SimpleGraph (V⊕U)
  | 0=>⊥
  | n+1=>ordinaryDeletionHistory R S n ⊔ ordinaryPhysicalGraph (R n) (S n)

theorem ordinary_deletion_history_adj (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (n:ℕ) (a b:V⊕U):
    (ordinaryDeletionHistory R S n).Adj a b ↔ ∃i<n,(ordinaryPhysicalGraph (R i) (S i)).Adj a b:=by
  induction n with
  | zero => simp [ordinaryDeletionHistory]
  | succ n ih =>
    rw [ordinaryDeletionHistory,SimpleGraph.sup_adj,ih]
    constructor
    · rintro (⟨i,hi,h⟩|h)
      · exact ⟨i,by omega,h⟩
      · exact ⟨n,by omega,h⟩
    · rintro ⟨i,hi,h⟩
      by_cases hne:i=n
      · subst i;exact Or.inr h
      · exact Or.inl ⟨i,by omega,h⟩

theorem ordinary_deletion_history_inner_zero
    (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ)
    (X:Finset V) (Z:Finset U) (Told:ℕ→Finset V) (Wold:ℕ→Finset U)
    (hX:∀i<n,X⊆Told i) (hZ:∀i<n,Z⊆Wold i)
    (havoid:∀i<n,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (Told i) (Wold i))):
    spanningRestriction (ordinaryDeletionHistory R S n) (ordinaryInnerVertices X Z)=⊥:=by
  apply le_antisymm
  · intro a b hab
    have hh:=(spanningRestriction_adj _ _ _ _).mp hab
    obtain ⟨i,hi,hedge⟩:=(ordinary_deletion_history_adj R S n a b).mp hh.1
    have hzero:=ordinary_protected_inner_zero_nested (R i) (S i) X (Told i) Z (Wold i)
      (hX i hi) (hZ i hi) (havoid i hi)
    have hedge':(spanningRestriction (ordinaryPhysicalGraph (R i) (S i)) (ordinaryInnerVertices X Z)).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hedge,hh.2.1,hh.2.2⟩
    rw [hzero] at hedge'
    exact hedge'
  · exact bot_le

def ordinaryHistoryRim (Q:SimpleGraph V) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ):SimpleGraph V:=
  Q\(ordinaryDeletionHistory R S n).comap Sum.inl

def ordinaryHistorySpokes (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ):V→U→Prop:=
  ordinarySpokesAfterPhysicalDeletion H (ordinaryDeletionHistory R S n)

theorem ordinary_history_rim_step (Q:SimpleGraph V) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ):
    ordinaryHistoryRim Q R S (n+1)=ordinaryHistoryRim Q R S n\R n:=by
  ext a b
  change (Q.Adj a b ∧ ¬((ordinaryDeletionHistory R S n).Adj (Sum.inl a) (Sum.inl b) ∨ (R n).Adj a b)) ↔
    ((Q.Adj a b ∧ ¬(ordinaryDeletionHistory R S n).Adj (Sum.inl a) (Sum.inl b)) ∧ ¬(R n).Adj a b)
  tauto

theorem ordinary_history_spokes_step (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ):
    ordinaryHistorySpokes H R S (n+1)=fun v u=>ordinaryHistorySpokes H R S n v u∧¬S n v u:=by
  funext v u
  apply propext
  change (H v u ∧ ¬((ordinaryDeletionHistory R S n).Adj (Sum.inl v) (Sum.inr u) ∨ S n v u)) ↔
    ((H v u ∧ ¬(ordinaryDeletionHistory R S n).Adj (Sum.inl v) (Sum.inr u)) ∧ ¬S n v u)
  tauto
end Oberwolfach
