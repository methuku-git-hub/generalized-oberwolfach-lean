module

public import Oberwolfach.TwoPathSwitchAlgebra
public import Oberwolfach.EvenSetPairing
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! The simultaneous colour switches repair all non-reserve degree parities
with a change of at most one at each vertex in each such colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem colour_path_switch_degree_identity {V R : Type*} [Fintype V] [DecidableEq V]
    [CommRing R] {q : ℕ} (m : Fin q → ℕ)
    (G : SimpleGraph V) (σ : Sym2 V → Fin (q+1))
    (x y z : ((j : Fin q)×Fin (m j)) → V)
    (hxy : ∀ i,x i≠y i)
    (hdisj : ∀ i j,i≠j → Disjoint (twoPathEdges (x i) (y i) (z i))
      (twoPathEdges (x j) (y j) (z j)))
    (hxz : ∀ i,G.Adj (x i) (z i)) (hyz : ∀ i,G.Adj (z i) (y i))
    (hc0 : ∀ i,σ s(x i,z i)=i.1.castSucc) (hc1 : ∀ i,σ s(z i,y i)=Fin.last q)
    (a : Fin q) (v : V) :
    let ι := twoPathEdgeEmbedding x y z hxy hdisj
    ((edgeColourGraph G (σ ∘ pairSwitchPermutation ι) a.castSucc).degree v:R)-
      ((edgeColourGraph G σ a.castSucc).degree v:R)=
      ∑ i : Fin (m a),((if y ⟨a,i⟩=v then (1:R) else 0)-(if x ⟨a,i⟩=v then 1 else 0)) := by
  intro ι
  have hh := twoPath_switch_degree_change (R:=R) G σ x y z hxy hdisj hxz hyz a.castSucc v
  dsimp only at hh
  rw [hh,Fintype.sum_sigma]
  have hneq : Fin.last q≠a.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last,Fin.val_castSucc] at hv
    omega
  simp only [hc0,hc1,hneq,ite_false,zero_sub]
  rw [Finset.sum_eq_single a]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [ite_true]
    ring
  · intro j _ hja
    have hn : j.castSucc≠a.castSucc := fun he => hja (Fin.castSucc_injective q he)
    simp only [hn,ite_false,neg_zero,mul_zero,Finset.sum_const_zero]
  · simp

theorem pairing_endpoint_discrepancy_bound {V : Type*} [DecidableEq V] {T : Finset V} {m : ℕ}
    (e : (Fin m×Bool)≃T) (v : V) :
    |∑ i : Fin m,((if (e (i,true)).val=v then (1:ℝ) else 0)-
      (if (e (i,false)).val=v then 1 else 0))|≤1 := by
  have hs := congrArg (fun t : ℕ => (t:ℝ)) (pairing_endpoint_sum e v)
  simp only [Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at hs
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb : (∑ i : Fin m,|(if (e (i,true)).val=v then (1:ℝ) else 0)-
      (if (e (i,false)).val=v then 1 else 0)|)≤
      ∑ i : Fin m,((if (e (i,false)).val=v then (1:ℝ) else 0)+
        (if (e (i,true)).val=v then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> norm_num
  apply hb.trans
  rw [hs]
  split_ifs <;> norm_num

theorem pairing_endpoint_discrepancy_mod_two {V : Type*} [DecidableEq V] {T : Finset V} {m : ℕ}
    (e : (Fin m×Bool)≃T) (v : V) :
    (∑ i : Fin m,((if (e (i,true)).val=v then (1:ZMod 2) else 0)-
      (if (e (i,false)).val=v then 1 else 0)))=if v∈T then 1 else 0 := by
  have hs := congrArg (fun t : ℕ => (t:ZMod 2)) (pairing_endpoint_sum e v)
  simp only [Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at hs
  simpa only [sub_eq_add_neg,ZMod.neg_eq_self_mod_two,add_comm] using hs

theorem degree_complement_add {V : Type*} [Fintype V]
    (G J : SimpleGraph V) (hJ : J≤G) (v : V) : (G\J).degree v+J.degree v=G.degree v := by
  classical
  have hsub : J.neighborFinset v⊆G.neighborFinset v := by
    intro u hu
    exact (G.mem_neighborFinset _ _).mpr (hJ ((J.mem_neighborFinset _ _).mp hu))
  simpa only [← SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_sdiff] using
    Finset.card_sdiff_add_card_eq_card hsub

theorem odd_indicator_zmod (n : ℕ) : (if Odd n then (1:ZMod 2) else 0)=(n:ZMod 2) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [if_neg (Nat.not_odd_iff_even.mpr he)]
    exact he.natCast_zmod_two.symm
  · rw [if_pos ho]
    exact ho.natCast_zmod_two.symm

end Oberwolfach
