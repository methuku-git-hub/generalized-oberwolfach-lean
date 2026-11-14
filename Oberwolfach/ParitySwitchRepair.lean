module

public import Oberwolfach.ParitySwitchDegrees
public import Oberwolfach.ColourReorientation

@[expose] public section

/-! Completing the finite parity repair, including the reserve colour.
The proof records exact class-size preservation and uniform degree losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem edgeColourGraph_degree_total {V : Type*} [Fintype V] {k : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin k) (v : V) :
    (∑ a,(edgeColourGraph G σ a).degree v)=G.degree v := by
  simp only [edgeColourGraph_degree,sampledColourDegree,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem edgeColourGraph_le {V : Type*} {k : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin k) (a : Fin k) : edgeColourGraph G σ a≤G := by
  intro u v h;exact h.1

theorem paired_colour_parity_repair {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : Even q) (G : SimpleGraph V) (σ : Sym2 V → Fin (q+1))
    (T : Fin q → Finset V) (m : Fin q → ℕ) (e : ∀ j,(Fin (m j)×Bool)≃T j)
    (hT : ∀ j v,v∈T j ↔ Odd ((G\edgeColourGraph G σ j.castSucc).degree v))
    (z : ((j : Fin q)×Fin (m j)) → V)
    (hdisj : ∀ i j,i≠j →
      Disjoint (twoPathEdges (e i.1 (i.2,false)).val (e i.1 (i.2,true)).val (z i))
        (twoPathEdges (e j.1 (j.2,false)).val (e j.1 (j.2,true)).val (z j)))
    (hxz : ∀ i,G.Adj (e i.1 (i.2,false)).val (z i))
    (hyz : ∀ i,G.Adj (z i) (e i.1 (i.2,true)).val)
    (hc0 : ∀ i,σ s((e i.1 (i.2,false)).val,z i)=i.1.castSucc)
    (hc1 : ∀ i,σ s(z i,(e i.1 (i.2,true)).val)=Fin.last q) :
    ∃ τ : Sym2 V → Fin (q+1),
      (∀ a,(edgeColourGraph G τ a).edgeFinset.card=(edgeColourGraph G σ a).edgeFinset.card) ∧
      (∀ a v,Even ((G\edgeColourGraph G τ a).degree v)) ∧
      (∀ a : Fin q,∀ v,|((edgeColourGraph G τ a.castSucc).degree v:ℝ)-
        ((edgeColourGraph G σ a.castSucc).degree v:ℝ)|≤1) ∧
      (∀ v,|((edgeColourGraph G τ (Fin.last q)).degree v:ℝ)-
        ((edgeColourGraph G σ (Fin.last q)).degree v:ℝ)|≤q) := by
  let x (i : (j : Fin q)×Fin (m j)) := (e i.1 (i.2,false)).val
  let y (i : (j : Fin q)×Fin (m j)) := (e i.1 (i.2,true)).val
  have hxy (i : (j : Fin q)×Fin (m j)) : x i≠y i := pairing_endpoints_distinct (e i.1) i.2
  let ι := twoPathEdgeEmbedding x y z hxy hdisj
  let τ := σ ∘ pairSwitchPermutation ι
  have hid (R : Type) [CommRing R] (a : Fin q) (v : V) :
      ((edgeColourGraph G τ a.castSucc).degree v:R)-((edgeColourGraph G σ a.castSucc).degree v:R)=
      ∑ i : Fin (m a),((if (e a (i,true)).val=v then (1:R) else 0)-
        (if (e a (i,false)).val=v then 1 else 0)) :=
    colour_path_switch_degree_identity m G σ x y z hxy hdisj hxz hyz hc0 hc1 a v
  have hbound (a : Fin q) (v : V) : |((edgeColourGraph G τ a.castSucc).degree v:ℝ)-
      ((edgeColourGraph G σ a.castSucc).degree v:ℝ)|≤1 := by
    rw [hid ℝ]
    exact pairing_endpoint_discrepancy_bound (e a) v
  have hmod (a : Fin q) (v : V) :
      ((edgeColourGraph G τ a.castSucc).degree v:ZMod 2)=(G.degree v:ZMod 2) := by
    have hi := hid (ZMod 2) a v
    rw [pairing_endpoint_discrepancy_mod_two] at hi
    simp only [hT,odd_indicator_zmod] at hi
    have hc := congrArg (fun n : ℕ => (n:ZMod 2))
      (degree_complement_add G (edgeColourGraph G σ a.castSucc) (edgeColourGraph_le G σ _) v)
    simp only [Nat.cast_add] at hc
    linear_combination hi+hc
  have hlast (R : Type) [CommRing R] (v : V) :
      (∑ a : Fin q,(((edgeColourGraph G τ a.castSucc).degree v:R)-
        ((edgeColourGraph G σ a.castSucc).degree v:R)))+
      (((edgeColourGraph G τ (Fin.last q)).degree v:R)-
        ((edgeColourGraph G σ (Fin.last q)).degree v:R))=0 := by
    have ht := congrArg (fun n : ℕ => (n:R)) (edgeColourGraph_degree_total G τ v)
    have hs := congrArg (fun n : ℕ => (n:R)) (edgeColourGraph_degree_total G σ v)
    simp only [Nat.cast_sum,Nat.cast_add,Fin.sum_univ_castSucc] at ht hs
    rw [Finset.sum_sub_distrib]
    linear_combination ht-hs
  have hmodall (a : Fin (q+1)) (v : V) :
      ((edgeColourGraph G τ a).degree v:ZMod 2)=(G.degree v:ZMod 2) := by
    refine Fin.lastCases ?_ (fun a => hmod a v) a
    have ht := congrArg (fun n : ℕ => (n:ZMod 2)) (edgeColourGraph_degree_total G τ v)
    simp only [Nat.cast_sum,Nat.cast_add,Fin.sum_univ_castSucc,hmod,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,hq.natCast_zmod_two,zero_mul,zero_add] at ht
    exact ht
  refine ⟨τ,?_,?_,hbound,?_⟩
  · intro a
    exact twoPath_switch_preserves_card G σ x y z hxy hdisj hxz hyz a
  · intro a v
    apply ZMod.natCast_eq_zero_iff_even.mp
    have hc := congrArg (fun n : ℕ => (n:ZMod 2))
      (degree_complement_add G (edgeColourGraph G τ a) (edgeColourGraph_le G τ a) v)
    simp only [Nat.cast_add,hmodall] at hc
    exact add_right_cancel (hc.trans (zero_add _).symm)
  · intro v
    have hh := hlast ℝ v
    have he : ((edgeColourGraph G τ (Fin.last q)).degree v:ℝ)-
        ((edgeColourGraph G σ (Fin.last q)).degree v:ℝ)=
        -(∑ a : Fin q,(((edgeColourGraph G τ a.castSucc).degree v:ℝ)-
          ((edgeColourGraph G σ a.castSucc).degree v:ℝ))) := by linarith only [hh]
    rw [he,abs_neg]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin q,(1:ℝ) := Finset.sum_le_sum (fun a _ => hbound a v)
      _ = _ := by simp

end Oberwolfach
