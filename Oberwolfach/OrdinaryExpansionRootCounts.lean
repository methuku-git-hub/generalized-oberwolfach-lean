module

public import Oberwolfach.OrdinaryExpansionDegrees
public import Oberwolfach.CanonicalEdgeDarts

@[expose] public section

/-! The actual edge and spoke identifiers satisfy the endpoint counts
required by the finite expansion construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem actual_edge_endpoint_count (G : SimpleGraph V) (a : V) :
    (Finset.univ.filter (fun e : G.edgeFinset => a=e.val.out.1)).card+
    (Finset.univ.filter (fun e : G.edgeFinset => a=e.val.out.2)).card=G.degree a := by
  rw [card_filter_naturalIndicator,card_filter_naturalIndicator,←Finset.sum_add_distrib]
  have hs : (∑ e : G.edgeFinset,naturalIndicator (a∈e.val))=G.degree a := by
    rw [Finset.sum_coe_sort G.edgeFinset (fun e : Sym2 V => naturalIndicator (a∈e))]
    calc
      _ = ∑ e∈G.edgeFinset,if a∈e then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : a∈e <;> simp [naturalIndicator,h]
      _ = (G.edgeFinset.filter (fun e => a∈e)).card := by
        rw [Finset.card_eq_sum_ones,Finset.sum_filter]
      _ = G.degree a := by rw [←G.incidenceFinset_eq_filter,G.card_incidenceFinset_eq_degree]
  rw [←hs]
  apply Finset.sum_congr rfl
  intro e _
  have he : s(e.val.out.1,e.val.out.2)=e.val := by rw [Sym2.mk];exact e.val.out_eq
  have hm : a∈e.val ↔ a=e.val.out.1 ∨ a=e.val.out.2 := by
    calc
      (a∈e.val) ↔ a∈s(e.val.out.1,e.val.out.2) := by rw [he]
      _ ↔ _ := Sym2.mem_iff
  have hn := (edge_out_adj G e).ne
  by_cases h1 : a=e.val.out.1 <;> by_cases h2 : a=e.val.out.2
  all_goals simp_all [naturalIndicator]

theorem actual_spoke_row_count (H : V → U → Prop) (a : V) :
    (Finset.univ.filter (fun j : {e : V×U // H e.1 e.2} => a=j.val.1)).card=
      (Finset.univ.filter (H a)).card := by
  let e : {j : {e : V×U // H e.1 e.2} // a=j.val.1} ≃ {b : U // H a b} := {
    toFun := fun j => ⟨j.val.val.2,by have h:=j.val.property;rw [←j.property] at h;exact h⟩
    invFun := fun b => ⟨⟨(a,b.val),b.property⟩,rfl⟩
    left_inv := by intro j;apply Subtype.ext;apply Subtype.ext;exact Prod.ext j.property rfl
    right_inv := by intro b;rfl }
  simpa only [Fintype.card_subtype] using Fintype.card_congr e

theorem actual_spoke_hub_count (H : V → U → Prop) (b : U) :
    (Finset.univ.filter (fun j : {e : V×U // H e.1 e.2} => b=j.val.2)).card=
      (Finset.univ.filter (fun a => H a b)).card := by
  let e : {j : {e : V×U // H e.1 e.2} // b=j.val.2} ≃ {a : V // H a b} := {
    toFun := fun j => ⟨j.val.val.1,by have h:=j.val.property;rw [←j.property] at h;exact h⟩
    invFun := fun a => ⟨⟨(a.val,b),a.property⟩,rfl⟩
    left_inv := by intro j;apply Subtype.ext;apply Subtype.ext;exact Prod.ext rfl j.property
    right_inv := by intro a;rfl }
  simpa only [Fintype.card_subtype] using Fintype.card_congr e

theorem actual_edge_spoke_expansion_balance {W : Type*} [Fintype W] [DecidableEq W]
    (C : SimpleGraph W) (z o : W) (hzo : C.Adj z o) (hC : C.IsRegularOfDegree 2)
    (G : SimpleGraph V) (H : V → U → Prop)
    (hbal : ∀ a,G.degree a=2*(Finset.univ.filter (H a)).card) :
    ∀ a,(ordinaryExpansionRim (J:={e : V×U // H e.1 e.2}) C z o
      (fun e : G.edgeFinset => e.val.out.1) (fun e : G.edgeFinset => e.val.out.2)).degree a=
      2*(Finset.univ.filter (ordinaryExpansionSpokes z
        (fun j : {e : V×U // H e.1 e.2} => j.val.1) (fun j => j.val.2) a)).card := by
  apply ordinaryExpansion_row_balance C z o hzo hC
  intro a
  rw [actual_edge_endpoint_count,actual_spoke_row_count,hbal]

theorem actual_edge_spoke_expansion_divisibility {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (hW : Fintype.card W=r)
    (z : W) (hdiv : ∀ b,r ∣ (Finset.univ.filter (fun a => H a b)).card) :
    ∀ b,r ∣ (Finset.univ.filter (fun a => ordinaryExpansionSpokes (E:=G.edgeFinset) z
      (fun j : {e : V×U // H e.1 e.2} => j.val.1) (fun j => j.val.2) a b)).card := by
  apply ordinaryExpansion_hub_divisibility r hW
  intro b
  rw [actual_spoke_hub_count]
  exact hdiv b

end Oberwolfach
