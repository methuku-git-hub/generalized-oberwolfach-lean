module

public import Oberwolfach.MarkedExtensionDomains
public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section

/-! Realized row counts for arbitrary rim and spoke relations. This
representation covers later deletions without changing any probability
law or the fixed domain in the original row estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def markedRelationRowCount (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (C : Finset V) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) : ℝ :=
  ∑ z∈C,if (∀ a∈S,R (markedRowRim a z)) ∧ (∀ a∈J,H a.1 z a.2) then 1 else 0

def markedOneExtensionSet (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (A : Finset V) (j : Bool) (v : V) (u : U) : Finset V :=
  A.filter (fun z=>R (if j then Sum.inr (v,z) else Sum.inl (v,z)) ∧ H j z u)

def markedTwoExtensionSet (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (A : Finset V) (j : Bool) (v w : V) (u : U) : Finset V :=
  A.filter (fun z=>R (Sum.inl (v,z)) ∧ R (if j then Sum.inr (z,w) else Sum.inl (z,w)) ∧ H false z u)

theorem markedRelationRowCount_card (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (C : Finset V) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) :
    markedRelationRowCount R H C S J=
      ((C.filter (fun z=>(∀ a∈S,R (markedRowRim a z)) ∧ (∀ a∈J,H a.1 z a.2))).card:ℝ) := by
  simp only [markedRelationRowCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem markedRelationRowCount_one_le (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (A C : Finset V) (hCA : C⊆A) (j : Bool) (v : V) (u : U) :
    markedRelationRowCount R H C (markedOneExtensionRequests j v) {(j,u)}≤
      ((markedOneExtensionSet R H A j v u).card:ℝ) := by
  rw [markedRelationRowCount_card]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzC,hr,hh⟩:=Finset.mem_filter.mp hz
  have hr':=hr (j,false,v) (by simp [markedOneExtensionRequests])
  have hh':=hh (j,u) (by simp)
  apply Finset.mem_filter.mpr
  exact ⟨hCA hzC,by simpa [markedRowRim] using hr',hh'⟩

theorem markedRelationRowCount_two_le (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop)
    (A C : Finset V) (hCA : C⊆A) (j : Bool) (v w : V) (u : U) :
    markedRelationRowCount R H C (markedTwoExtensionRequests j v w) {(false,u)}≤
      ((markedTwoExtensionSet R H A j v w u).card:ℝ) := by
  rw [markedRelationRowCount_card]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzC,hr,hh⟩:=Finset.mem_filter.mp hz
  have hr₀:=hr (false,false,v) (by simp [markedTwoExtensionRequests])
  have hr₁:=hr (j,true,w) (by simp [markedTwoExtensionRequests])
  have hh':=hh (false,u) (by simp)
  apply Finset.mem_filter.mpr
  exact ⟨hCA hzC,by simpa [markedRowRim] using hr₀,by simpa [markedRowRim] using hr₁,hh'⟩

theorem markedRelationRowCount_withSpokes {Γ Color : Type} [Fintype Γ] [Fintype Color]
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (C : Finset V) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) :
    markedRelationRowCount (rawMarkedPairRims P π d σ) H C S J=
      markedRowCountWithSpokes P π d σ H C S J := rfl

theorem markedOneExtensionRequests_product (j : Bool) (v : V) (u : U) (p k s t : ℝ) :
    (∏ a∈markedOneExtensionRequests j v,if a.1 then k else p)*
      (∏ a∈({(j,u)}:Finset (Bool×U)),if a.1 then t else s)=
      (if j then k else p)*(if j then t else s) := by simp [markedOneExtensionRequests]

theorem markedTwoExtensionRequests_product (j : Bool) (v w : V) (u : U) (p k s t : ℝ) :
    (∏ a∈markedTwoExtensionRequests j v w,if a.1 then k else p)*
      (∏ a∈({(false,u)}:Finset (Bool×U)),if a.1 then t else s)=
      p*(if j then k else p)*s := by
  simp [markedTwoExtensionRequests]

theorem marked_two_extension_edges_distinct (π : Equiv.Perm V) (j : Bool) (v w z : V)
    (hne : v≠if j then π w else w) : s(v,z)≠s(z,if j then π w else w) := by
  intro he
  exact hne (Sym2.congr_left.mp (he.trans Sym2.eq_swap))

end Oberwolfach
