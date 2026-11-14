module

public import Oberwolfach.MarkedPairParentSums

@[expose] public section

/-! Root loads of a fixed tuple weighting in the unrestricted parent hub
domain. A spoke fixes one hub; a rim sums over all hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  (m b : ℕ) (π : Equiv.Perm V) (weight : (Fin (m+1)→V)→ℝ)
  (hsupport : ∀ C,¬PermutationSeparated π b C → weight C=0)

include hsupport

theorem markedParent_spoke_position_load (j : Bool) (v : V) (u : U) :
    (∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun (_ : V) (_ : U)=>True) (fun _ _=>True),
      if Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W then weight W.1.val else 0)=
    ∑ i : Fin (m+1),if decide (i=0)=j then
      (∑ C : Fin (m+1)→V,if C i=v then weight C else 0) else 0 := by
  have he (W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun (_ : V) (_ : U)=>True) (fun _ _=>True)) := typedMarkedSpoke_position_sum W (weight W.1.val) j v u
  simp only [typedMarkedOccurrenceResources_spoke] at he ⊢
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [markedPairWheel_sum m b π
    (fun C z=>if decide (i=0)=j ∧ C i=v ∧ z=u then weight C else 0)
    (by intro C z hC;simp only [hsupport C hC,ite_self])]
  by_cases hi : decide (i=0)=j
  · simp only [hi,true_and,ite_true]
    apply Finset.sum_congr rfl
    intro C _
    by_cases hv : C i=v
    · simp [hv]
    · simp [hv]
  · simp [hi]

theorem markedParent_marked_rim_position_load (x y : V) :
    (∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun (_ : V) (_ : U)=>True) (fun _ _=>True),
      if Sum.inl (Sum.inr (x,y))∈typedMarkedOccurrenceResources W then weight W.1.val else 0)=
    (Fintype.card U:ℝ)*∑ C : Fin (m+1)→V,
      if C (Fin.last m)=x ∧ C 0=y then weight C else 0 := by
  trans ∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
    (fun (_ : V) (_ : U)=>True) (fun _ _=>True),if W.1.val (Fin.last m)=x ∧ W.1.val 0=y then weight W.1.val else 0
  · apply Finset.sum_congr rfl
    intro W _
    have he := typedMarkedRim_position_sum W (weight W.1.val) (Sum.inr (x,y))
    simp only [typedMarkedOccurrenceResources_rim] at he ⊢
    rw [he,Fin.sum_univ_castSucc]
    simp only [markedPairCycle_edge_ordinary,markedPairCycle_edge_marked,Sum.inl_ne_inr,ite_false,
      Finset.sum_const_zero,zero_add,Sum.inr.injEq,Prod.mk.injEq]
  · rw [markedPairWheel_sum m b π
      (fun C (_ : U)=>if C (Fin.last m)=x ∧ C 0=y then weight C else 0)
      (by intro C z hC;simp only [hsupport C hC,ite_self])]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mul_sum]

theorem markedParent_ordinary_rim_position_load (x y : V) :
    (∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun (_ : V) (_ : U)=>True) (fun _ _=>True),
      if Sum.inl (Sum.inl (x,y))∈typedMarkedOccurrenceResources W then weight W.1.val else 0)=
    (Fintype.card U:ℝ)*∑ i : Fin m,∑ C : Fin (m+1)→V,
      if C i.castSucc=x ∧ C i.succ=y then weight C else 0 := by
  trans ∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
    (fun (_ : V) (_ : U)=>True) (fun _ _=>True),∑ i : Fin m,
      if W.1.val i.castSucc=x ∧ W.1.val i.succ=y then weight W.1.val else 0
  · apply Finset.sum_congr rfl
    intro W _
    have he := typedMarkedRim_position_sum W (weight W.1.val) (Sum.inl (x,y))
    simp only [typedMarkedOccurrenceResources_rim] at he ⊢
    rw [he,Fin.sum_univ_castSucc]
    simp only [markedPairCycle_edge_ordinary,markedPairCycle_edge_marked,Sum.inr_ne_inl,ite_false,
      add_zero,Sum.inl.injEq,Prod.mk.injEq]
  · rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [markedPairWheel_sum m b π
      (fun C (_ : U)=>if C i.castSucc=x ∧ C i.succ=y then weight C else 0)
      (by intro C z hC;simp only [hsupport C hC,ite_self])]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mul_sum]

end Oberwolfach
