module

public import Oberwolfach.OrdinaryWheelResources
public import Oberwolfach.OrdinaryWheelCodegrees

@[expose] public section

/-! Restriction of the wheel hypergraph to the physical edges of its host.
Every retained vertex has fractional degree one; absent host edges are not
inserted as isolated vertices in a matching theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}

abbrev OrdinaryActiveEdge (Q : SimpleGraph V) (H : V → U → Prop) :=
  {e : Sym2 V⊕(V×U) // ordinaryResourceState Q H e=true}

def ordinaryActiveResources (W : OrdinaryWheel Q F H r) : Finset (OrdinaryActiveEdge Q H) :=
  (ordinaryWheelResources W).subtype (fun e=>ordinaryResourceState Q H e=true)

theorem ordinaryWheelResources_present (W : OrdinaryWheel Q F H r)
    (e : Sym2 V⊕(V×U)) (he : e∈ordinaryWheelResources W) : ordinaryResourceState Q H e=true := by
  cases e with
  | inl e =>
    rw [ordinaryWheelResources_rim] at he
    have hq : e∈Q.edgeSet := SimpleGraph.edgeSet_mono W.val.1.property he
    simpa only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq] using hq
  | inr vu =>
    rcases vu with ⟨v,u⟩
    rw [ordinaryWheelResources_spoke] at he
    have hh : H v u := by
      rw [← he.1]
      exact W.property.1 v he.2
    simpa only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq] using hh

theorem ordinaryActiveResources_mem (W : OrdinaryWheel Q F H r) (e : OrdinaryActiveEdge Q H) :
    e∈ordinaryActiveResources W ↔ e.val∈ordinaryWheelResources W := Finset.mem_subtype

theorem ordinaryActiveResources_map (W : OrdinaryWheel Q F H r) :
    (ordinaryActiveResources W).map (Function.Embedding.subtype _) =ordinaryWheelResources W :=
  Finset.subtype_map_of_mem (ordinaryWheelResources_present W)

theorem ordinaryActiveResources_card (W : OrdinaryWheel Q F H r) :
    (ordinaryActiveResources W).card=2*r := by
  have hh := congrArg Finset.card (ordinaryActiveResources_map W)
  simpa only [Finset.card_map,ordinaryWheelResources_card] using hh

theorem ordinaryActiveResources_injective :
    Function.Injective (ordinaryActiveResources (Q:=Q) (F:=F) (H:=H) (r:=r)) := by
  intro W Z he
  apply ordinaryWheelResources_injective
  rw [← ordinaryActiveResources_map W,← ordinaryActiveResources_map Z,he]

theorem ordinary_active_exact_loads (w : OrdinaryWheel Q F H r → ℝ)
    (hrim : ∀ x y,ordinaryRimLoad w x y=if Q.Adj x y then 1 else 0)
    (hspoke : ∀ v u,ordinarySpokeLoad w v u=if H v u then 1 else 0)
    (e : OrdinaryActiveEdge Q H) : (∑ W,if e∈ordinaryActiveResources W then w W else 0)=1 := by
  rcases e with ⟨e,he⟩
  simp only [ordinaryActiveResources_mem]
  cases e with
  | inl e =>
    induction e using Sym2.ind with
    | _ x y =>
      have hq : Q.Adj x y := by simpa only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq,SimpleGraph.mem_edgeSet] using he
      rw [ordinaryWheelResources_load_rim,hrim,if_pos hq]
  | inr vu =>
    rcases vu with ⟨v,u⟩
    have hh : H v u := by simpa only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq] using he
    rw [ordinaryWheelResources_load_spoke,hspoke,if_pos hh]

theorem ordinary_active_pair_loads (hr : 2≤r) (hn : 0<Fintype.card V)
    (hu : Fintype.card U≤Fintype.card V) (w : OrdinaryWheel Q F H r → ℝ) (B : ℝ)
    (hB : 0≤B) (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (e f : OrdinaryActiveEdge Q H) (hef : e≠f) :
    (∑ W,if e∈ordinaryActiveResources W ∧ f∈ordinaryActiveResources W then w W else 0)≤
      (r:ℝ)^4*B/Fintype.card V := by
  simp only [ordinaryActiveResources_mem]
  exact ordinary_wheel_physical_pair_load Q F H r hr hn hu w B hB hw e.val f.val
    (fun hh=>hef (Subtype.ext hh))

end Oberwolfach
