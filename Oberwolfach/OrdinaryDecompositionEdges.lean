module

public import Oberwolfach.ResourceDecompositions
public import Oberwolfach.OrdinaryWheelRestriction

@[expose] public section

/-! Physical edge sets for ordinary wheel decompositions. Rim edges
remain unordered pairs in V and spokes remain ordered V-U pairs; the
two types cannot be identified by a decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryHostResources (Q : SimpleGraph V) (H : V → U → Prop) : Finset (Sym2 V ⊕ (V×U)) :=
  Finset.univ.filter (fun e => ordinaryResourceState Q H e=true)

theorem ordinaryHostResources_rim (Q : SimpleGraph V) (H : V → U → Prop) (e : Sym2 V) :
    Sum.inl e∈ordinaryHostResources Q H ↔ e∈Q.edgeSet := by
  simp [ordinaryHostResources,ordinaryResourceState]

theorem ordinaryHostResources_spoke (Q : SimpleGraph V) (H : V → U → Prop) (v : V) (u : U) :
    Sum.inr (v,u)∈ordinaryHostResources Q H ↔ H v u := by
  simp [ordinaryHostResources,ordinaryResourceState]

theorem ordinaryHostResources_union (Q P : SimpleGraph V) (H K : V → U → Prop) :
    ordinaryHostResources (Q⊔P) (fun v u => H v u ∨ K v u)=ordinaryHostResources Q H ∪ ordinaryHostResources P K := by
  ext e
  cases e with
  | inl e => simp only [Finset.mem_union,ordinaryHostResources_rim,SimpleGraph.edgeSet_sup,Set.mem_union]
  | inr vu => rcases vu with ⟨v,u⟩; simp only [Finset.mem_union,ordinaryHostResources_spoke]

theorem ordinaryHostResources_sdiff (Q P : SimpleGraph V) (H K : V → U → Prop) :
    ordinaryHostResources (Q\P) (fun v u => H v u ∧ ¬K v u)=ordinaryHostResources Q H \ ordinaryHostResources P K := by
  ext e
  cases e with
  | inl e => simp only [Finset.mem_sdiff,ordinaryHostResources_rim,SimpleGraph.edgeSet_sdiff,Set.mem_diff]
  | inr vu => rcases vu with ⟨v,u⟩; simp only [Finset.mem_sdiff,ordinaryHostResources_spoke]

theorem ordinaryHostResources_injective (Q P : SimpleGraph V) (H K : V → U → Prop)
    (h : ordinaryHostResources Q H=ordinaryHostResources P K) : Q=P ∧ H=K := by
  constructor
  · apply SimpleGraph.ext
    funext v w
    have hh := congrArg (fun S => Sum.inl s(v,w)∈S) h
    simpa only [ordinaryHostResources_rim,SimpleGraph.mem_edgeSet] using hh
  · funext v u
    have hh := congrArg (fun S => Sum.inr (v,u)∈S) h
    simpa only [ordinaryHostResources_spoke] using hh

theorem ordinaryWheelResources_subset_host {P F : SimpleGraph V} {Hbase : V → U → Prop} {r : ℕ}
    (W : OrdinaryWheel P F Hbase r) (Q : SimpleGraph V) (H : V → U → Prop) :
    ordinaryWheelResources W ⊆ ordinaryHostResources Q H ↔ OrdinaryWheelSurvives W Q H := by
  change (∀ e∈ordinaryWheelResources W,e∈ordinaryHostResources Q H) ↔ _
  simpa only [ordinaryHostResources,Finset.mem_filter,Finset.mem_univ,true_and] using
    (ordinaryWheelSurvives_iff_resources (Q:=Q) (H:=H) W).symm

abbrev UniversalOrdinaryWheel (V U : Type*) (r : ℕ) :=
  OrdinaryWheel (⊤ : SimpleGraph V) (⊥ : SimpleGraph V) (fun (_ : V) (_ : U) => True) r

def ordinaryWheelUniversal {P F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : OrdinaryWheel P F H r) : UniversalOrdinaryWheel V U r :=
  ⟨(⟨W.val.1.val,le_top⟩,W.val.2),fun _ _ => trivial,fun _ _ _ _ => not_false⟩

theorem ordinaryWheelUniversal_resources {P F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : OrdinaryWheel P F H r) : ordinaryWheelResources (ordinaryWheelUniversal W)=ordinaryWheelResources W := rfl

theorem ordinaryWheelUniversal_injective {P F : SimpleGraph V} {H : V → U → Prop} {r : ℕ} :
    Function.Injective (ordinaryWheelUniversal (P:=P) (F:=F) (H:=H) (r:=r)) := by
  intro W Z he
  apply ordinaryWheelResources_injective
  have hh := congrArg (fun Y : UniversalOrdinaryWheel V U r => ordinaryWheelResources Y) he
  simpa only [ordinaryWheelUniversal_resources] using hh

def HasOrdinaryWheelDecomposition (Q : SimpleGraph V) (H : V → U → Prop) (r : ℕ) : Prop :=
  HasResourceDecomposition (ordinaryWheelResources (P:=⊤) (F:=⊥) (Hbase:=fun (_ : V) (_ : U) => True) (r:=r))
    (ordinaryHostResources Q H)

end Oberwolfach
