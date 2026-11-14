module

public import Oberwolfach.MarkedCycleIncidence
public import Oberwolfach.CopiedMarkedCapacities
public import Oberwolfach.FixedCoordinateCounts

@[expose] public section

/-! A fixed directed edge fixes two distinct positions. This gives the
uniform incidence bound used for the positive preliminary cycle weighting. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_subtype_sum_le {I : Type*} [Fintype I] (p : I → Prop)
    (f : I → ℝ) (hf : ∀ i,0≤f i) : (∑ i : {i // p i},f i.val)≤∑ i,f i := by
  have he := Fintype.sum_subtype_add_sum_subtype p f
  have hn : 0≤∑ i : {i // ¬p i},f i.val := Finset.sum_nonneg (fun _ _ => hf _)
  linarith

theorem two_position_indicator_total {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I]
    (i j : I) (hij : i≠j) (x y : V) :
    (∑ C : I → V,if C i=x ∧ C j=y then (1:ℝ) else 0)=(Fintype.card V:ℝ)^(Fintype.card I-2) := by
  classical
  let a := Function.update (fun _ : I => y) i x
  have hp (C : I → V) : (∀ r∈({i,j}:Finset I),C r=a r) ↔ C i=x ∧ C j=y := by
    simp [a,Function.update_apply,hij,Ne.symm hij]
  have hcard : ({i,j}:Finset I).card=2 := by simp [hij]
  let S : Set (I → V) := {C | ∀ r∈({i,j}:Finset I),C r=a r}
  have he := Finset.sum_congr_set S
    (fun C => if C i=x ∧ C j=y then (1:ℝ) else 0) (fun _ : S => (1:ℝ))
    (by intro C hC;exact if_pos ((hp C).mp hC))
    (by intro C hC;exact if_neg (fun h => hC ((hp C).mpr h)))
  rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  change (Fintype.card {C : I → V // ∀ r∈({i,j}:Finset I),C r=a r}:ℝ)=_
  rw [fixedCoordinates_card,hcard,Nat.cast_pow]

theorem marked_cycle_incidence_count {V E K : Type*} [Fintype V] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (hm : 1≤m)
    (π : Equiv.Perm V) (b : ℕ) (e : E⊕K) :
    (∑ C : MarkedCycleTuple tail head ktail khead m π b,
      markedCycleIncidence tail head ktail khead m C.val e)≤
      (m:ℝ)*(Fintype.card V:ℝ)^(m-1) := by
  classical
  apply (finite_subtype_sum_le (IsMarkedCycleTuple tail head ktail khead m π b)
    (fun C => markedCycleIncidence tail head ktail khead m C e)
    (fun C => markedCycleIncidence_nonneg tail head ktail khead m C e)).trans
  cases e with
  | inl e =>
    simp only [markedCycleIncidence,Sum.elim_inl]
    rw [Finset.sum_comm]
    have hh (j : Fin m) :
        (∑ C : Fin (m+1) → V,directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e)=
          (Fintype.card V:ℝ)^(m-1) := by
      have hjs : j.castSucc≠j.succ := by intro he;have := congrArg Fin.val he;simp only [Fin.val_castSucc,Fin.val_succ] at this;omega
      have he := two_position_indicator_total j.castSucc j.succ hjs (tail e) (head e)
      simpa only [directedEdgeIndicator,eq_comm,Fintype.card_fin,show m+1-2=m-1 by omega] using he
    simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,le_refl]
  | inr e =>
    simp only [markedCycleIncidence,Sum.elim_inr]
    have hne : (Fin.last m:Fin (m+1))≠0 := by intro he;have := congrArg Fin.val he;simp at this;omega
    have he := two_position_indicator_total (Fin.last m) 0 hne (ktail e) (khead e)
    have he' : (∑ C : Fin (m+1) → V,directedEdgeIndicator ktail khead (C (Fin.last m)) (C 0) e)=
        (Fintype.card V:ℝ)^(m-1) := by
      simpa only [directedEdgeIndicator,eq_comm,Fintype.card_fin,show m+1-2=m-1 by omega] using he
    rw [he']
    have hmr : (1:ℝ)≤m := by exact_mod_cast hm
    nlinarith [show 0≤(Fintype.card V:ℝ)^(m-1) by positivity]

end Oberwolfach
