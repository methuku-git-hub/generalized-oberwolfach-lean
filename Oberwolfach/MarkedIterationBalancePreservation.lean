module

public import Oberwolfach.MarkedFiniteInducedDomainBalance

@[expose] public section

/-! The next restricted balances are charged only to the deleted star.
All roots remain in the ambient sets. At roots of the protected inner
pair the balance is unchanged when no induced inner edge is deleted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteDomainBalance_star
    (tail head : E→V) (ktail khead : K→V) (HK : V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (m : ℕ) (X : Finset V) (Z : Finset U)
    (z : V⊕U) (i : Fin 4) :
    markedFiniteDomainBalance tail head ktail khead HK
      (A.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X))
      (S.filter (fun s=>s.1∈X ∨ s.2∈Z)) m X Z z i =
      markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i := by
  cases z with
  | inl v =>
    have ha : (A.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X)).filter
        (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈X)=
        A.filter (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈X) := by
      ext a
      simp only [Finset.mem_filter]
      split_ifs <;> tauto
    have hs : (S.filter (fun s=>s.1∈X ∨ s.2∈Z)).filter (fun s=>s.2∈Z)=S.filter (fun s=>s.2∈Z) := by
      ext s;simp only [Finset.mem_filter];tauto
    dsimp only [markedFiniteDomainBalance]
    rw [ha,hs]
  | inr u =>
    have hs : (S.filter (fun s=>s.1∈X ∨ s.2∈Z)).filter (fun s=>s.1∈X)=S.filter (fun s=>s.1∈X) := by
      ext s;simp only [Finset.mem_filter];tauto
    dsimp only [markedFiniteDomainBalance]
    rw [hs]

theorem markedFiniteDomainBalance_zero_inside_of_empty_induced
    (tail head : E→V) (ktail khead : K→V) (HK : V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (m : ℕ) (X : Finset V) (Z : Finset U)
    (hA : A.filter (fun a=>Sum.elim tail ktail a∈X ∧ Sum.elim head khead a∈X)=∅)
    (hS : S.filter (fun s=>s.1∈X ∧ s.2∈Z)=∅)
    (z : V⊕U) (hz : Sum.elim (fun v=>v∈X) (fun u=>u∈Z) z) (i : Fin 4) :
    markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i=0 := by
  have h := markedFiniteDomainBalance_induced_inside tail head ktail khead HK A S m X X Z Z
    (Finset.Subset.refl _) (Finset.Subset.refl _) z hz i
  rw [hA,hS] at h
  rw [← h]
  cases z <;> fin_cases i <;> simp [markedFiniteDomainBalance,markedFiniteBalance]

theorem marked_iteration_restricted_balance_preservation
    (tail head : E→V) (ktail khead : K→V) (HK : V→U→Prop)
    (A EA : Finset (E⊕K)) (S ES : Finset (V×U)) (m : ℕ) (X : Finset V) (Z : Finset U)
    (hEA : EA⊆A) (hES : ES⊆S)
    (hInnerA : EA.filter (fun a=>Sum.elim tail ktail a∈X ∧ Sum.elim head khead a∈X)=∅)
    (hInnerS : ES.filter (fun s=>s.1∈X ∧ s.2∈Z)=∅)
    (δ err : ℝ) (hδ : 0≤δ)
    (hA : ∀ v,(((EA.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X)).filter
      (fun a=>Sum.elim tail ktail a=v ∨ Sum.elim head khead a=v)).card : ℝ)≤δ)
    (hR : ∀ v,(((ES.filter (fun s=>s.1∈X ∨ s.2∈Z)).filter (fun s=>s.1=v)).card : ℝ)≤δ)
    (hC : ∀ u,(((ES.filter (fun s=>s.1∈X ∨ s.2∈Z)).filter (fun s=>s.2=u)).card : ℝ)≤δ)
    (hBal : ∀ z i, |markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i|≤err) :
    (∀ z i, |markedFiniteDomainBalance tail head ktail khead HK (A\EA) (S\ES) m X Z z i|≤err+(m+2)*δ) ∧
    (∀ z,Sum.elim (fun v=>v∈X) (fun u=>u∈Z) z→∀ i,
      markedFiniteDomainBalance tail head ktail khead HK (A\EA) (S\ES) m X Z z i=
        markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i) ∧
    (A\EA).filter (fun a=>Sum.elim tail ktail a∈X ∧ Sum.elim head khead a∈X)=
      A.filter (fun a=>Sum.elim tail ktail a∈X ∧ Sum.elim head khead a∈X) ∧
    (S\ES).filter (fun s=>s.1∈X ∧ s.2∈Z)=S.filter (fun s=>s.1∈X ∧ s.2∈Z) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro z i
    rw [markedFiniteDomainBalance_sdiff tail head ktail khead HK A EA S ES m X Z hEA hES z i]
    have hb := markedFiniteDomainBalance_bound tail head ktail khead HK
      (EA.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X))
      (ES.filter (fun s=>s.1∈X ∨ s.2∈Z)) m X Z δ hδ hA hR hC z i
    rw [markedFiniteDomainBalance_star] at hb
    exact (abs_sub _ _).trans (add_le_add (hBal z i) hb)
  · intro z hz i
    rw [markedFiniteDomainBalance_sdiff tail head ktail khead HK A EA S ES m X Z hEA hES z i,
      markedFiniteDomainBalance_zero_inside_of_empty_induced tail head ktail khead HK EA ES m X Z hInnerA hInnerS z hz i,
      sub_zero]
  · rw [finite_filter_set_sdiff,hInnerA,Finset.sdiff_empty]
  · rw [finite_filter_set_sdiff,hInnerS,Finset.sdiff_empty]

theorem marked_iteration_balance_normalized
    (m : ℕ) (δ σ ε η n a : ℝ) (hε : 0<ε) (hn : 0≤n)
    (ha : ε*n/2≤a) (hmargin : δ+2*(m+2)*σ/ε≤η) (hσ : 0≤σ) :
    δ*a+(m+2)*σ*n≤η*a := by
  have ha0 : 0≤a := (by positivity : 0≤ε*n/2).trans ha
  have hscale := mul_le_mul_of_nonneg_left ha (show 0≤2*(m+2)*σ/ε by positivity)
  have hbound := mul_le_mul_of_nonneg_right hmargin ha0
  have heq : (2*(m+2:ℝ)*σ/ε)*(ε*n/2)=(m+2)*σ*n := by field_simp <;> ring
  rw [heq] at hscale
  nlinarith only [hscale,hbound]

end Oberwolfach
