module

public import Oberwolfach.GraphRecolouring
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Exact edge-count congruences in the divisible-complement construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residue_increment (h M k : ℕ) (hh : 0<h) :
    ∃ a : ℕ,a<h ∧ (k+a)%h=M%h := by
  let a := (M%h+h-k%h)%h
  refine ⟨a,Nat.mod_lt _ hh,?_⟩
  have hk := Nat.mod_lt k hh
  have he : k%h+(M%h+h-k%h)=M%h+h := by omega
  have hr := congrArg (fun x => x%h) he
  simpa only [a,Nat.add_mod,Nat.mod_mod,Nat.mod_self,add_zero] using hr

theorem edgeColourGraph_card_total {V : Type*} [Fintype V] {k : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin k) :
    (∑ a,(edgeColourGraph G σ a).edgeFinset.card)=G.edgeFinset.card := by
  simp only [edgeColourGraph_edges,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem edge_complement_card_add {V : Type*} [Fintype V] [DecidableEq V]
    (G J : SimpleGraph V) (hJ : J≤G) : (G\J).edgeFinset.card+J.edgeFinset.card=G.edgeFinset.card := by
  have hsub : J.edgeFinset⊆G.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ u v => exact SimpleGraph.mem_edgeFinset.mpr (hJ (SimpleGraph.mem_edgeFinset.mp he))
  have he : (G\J).edgeFinset=G.edgeFinset\J.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v => simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.sdiff_adj,Finset.mem_sdiff]
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card hsub

theorem all_colour_residues_of_nonreserve {V : Type*} [Fintype V] {q h : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin (q+1)) (hhq : h∣q)
    (hres : ∀ a : Fin q,((edgeColourGraph G σ a.castSucc).edgeFinset.card:ZMod h)=
      (G.edgeFinset.card:ZMod h)) :
    ∀ a : Fin (q+1),((edgeColourGraph G σ a).edgeFinset.card:ZMod h)=(G.edgeFinset.card:ZMod h) := by
  intro a
  refine Fin.lastCases ?_ hres a
  have ht := congrArg (fun n : ℕ => (n:ZMod h)) (edgeColourGraph_card_total G σ)
  have hq0 : (q:ZMod h)=0 := (ZMod.natCast_eq_zero_iff q h).mpr hhq
  simp only [Nat.cast_sum,Nat.cast_add,Fin.sum_univ_castSucc,hres,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hq0,zero_mul,zero_add] at ht
  exact ht

theorem complement_edge_divisible_of_residue {V : Type*} [Fintype V] [DecidableEq V] (G J : SimpleGraph V)
    (hJ : J≤G) (h : ℕ) (hres : (J.edgeFinset.card:ZMod h)=(G.edgeFinset.card:ZMod h)) :
    h∣(G\J).edgeFinset.card := by
  apply (ZMod.natCast_eq_zero_iff _ h).mp
  have hc := congrArg (fun n : ℕ => (n:ZMod h)) (edge_complement_card_add G J hJ)
  simp only [Nat.cast_add,hres] at hc
  exact add_right_cancel (hc.trans (zero_add _).symm)

end Oberwolfach
