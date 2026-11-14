module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-! Pairing the vertices with wrong degree parity. Each vertex is an endpoint
at most once per colour; middle-vertex usage is accounted for separately. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem even_finset_pairing {V : Type*} (T : Finset V) (hT : Even T.card) :
    ∃ m : ℕ,T.card=2*m ∧ Nonempty ((Fin m×Bool)≃T) := by
  obtain ⟨m,hm⟩ := hT
  refine ⟨m,by omega,?_⟩
  apply Nonempty.intro
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe]
  omega

theorem pairing_endpoints_distinct {V : Type*} {T : Finset V} {m : ℕ}
    (e : (Fin m×Bool)≃T) (i : Fin m) :
    (e (i,false)).val≠(e (i,true)).val := by
  intro h
  have hh := e.injective (Subtype.ext h)
  exact Bool.false_ne_true (congrArg Prod.snd hh)

theorem pairing_endpoint_sum {V : Type*} [DecidableEq V] {T : Finset V} {m : ℕ}
    (e : (Fin m×Bool)≃T) (v : V) :
    (∑ i : Fin m,((if (e (i,false)).val=v then 1 else 0)+
      (if (e (i,true)).val=v then 1 else 0)):ℕ)=if v∈T then 1 else 0 := by
  have hh := e.sum_comp (fun z : T => if z.val=v then (1:ℕ) else 0)
  rw [Fintype.sum_prod_type] at hh
  simp only [Fintype.sum_bool] at hh
  have hf : (∑ z : T,if z.val=v then (1:ℕ) else 0)=if v∈T then 1 else 0 := by
    by_cases hv : v∈T
    · rw [if_pos hv,Finset.sum_eq_single (⟨v,hv⟩:T)]
      · simp
      · intro z _ hz
        have hn : z.val≠v := fun he => hz (Subtype.ext he)
        simp [hn]
      · simp
    · rw [if_neg hv]
      apply Finset.sum_eq_zero
      intro z _
      have hn : z.val≠v := fun he => hv (he ▸ z.property)
      simp [hn]
  simpa only [add_comm] using hh.trans hf

theorem pairing_endpoint_counts {V : Type*} [DecidableEq V] {T : Finset V} {m : ℕ}
    (e : (Fin m×Bool)≃T) (v : V) :
    (Finset.univ.filter (fun i : Fin m => (e (i,false)).val=v)).card+
      (Finset.univ.filter (fun i : Fin m => (e (i,true)).val=v)).card=
      if v∈T then 1 else 0 := by
  simpa only [Finset.card_filter,Finset.sum_add_distrib] using pairing_endpoint_sum e v

theorem paired_family_endpoint_bound {V J : Type*} [DecidableEq V] [Fintype J]
    (T : J → Finset V) (m : J → ℕ) (e : ∀ j,(Fin (m j)×Bool)≃T j)
    (v : V) (b : Bool) :
    (Finset.univ.filter (fun i : (j : J)×Fin (m j) => (e i.1 (i.2,b)).val=v)).card≤Fintype.card J := by
  classical
  have hf (j : J) : (∑ i : Fin (m j),if (e j (i,b)).val=v then (1:ℕ) else 0)≤1 := by
    have hh := pairing_endpoint_sum (e j) v
    rw [Finset.sum_add_distrib] at hh
    cases b <;> split_ifs at hh <;> omega
  simp only [Finset.card_filter,Fintype.sum_sigma]
  calc
    _ ≤ ∑ _ : J,(1:ℕ) := Finset.sum_le_sum (fun j _ => hf j)
    _ = _ := by simp

theorem odd_complement_degree_set_even {V : Type*} [Fintype V]
    (G J : SimpleGraph V) :
    Even ((Finset.univ.filter (fun v => Odd ((G\J).degree v))).card) := by
  simpa using (G\J).even_card_odd_degree_vertices

end Oberwolfach
