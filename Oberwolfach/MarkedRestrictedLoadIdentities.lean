module

public import Oberwolfach.MarkedSurvivalEquivalence
public import Oberwolfach.MarkedPotentialDegreeStability

@[expose] public section

/-! The actual rim and spoke loads in the restricted typed host equal the
fixed-weight potential sums at surviving roots. The parent map and the
physical permutation are retained exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

theorem markedPhysicalEdge_restrict (PE : E → Prop) (PK : K → Prop)
    (e : {e // PE e}⊕{e // PK e}) :
    markedPhysicalEdge (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π e=
      markedPhysicalEdge tail head ktail khead π (Sum.map Subtype.val Subtype.val e) := by
  cases e <;> rfl

theorem markedPhysicalEdge_restrict_injective (PE : E → Prop) (PK : K → Prop)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedPhysicalEdge (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π) := by
  intro e f hef
  rw [markedPhysicalEdge_restrict PE PK,markedPhysicalEdge_restrict PE PK] at hef
  exact (Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩) (hp hef)

theorem markedPotentialLoad_parent
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : (E⊕K)⊕(V×U)) :
    markedPotentialLoad w (fun _=>True) (fun v u=>H₀ v u ∨ Hₖ v u) e=
      ∑ W,if Sum.map (markedPhysicalEdge tail head ktail khead π) id e∈markedWheelPhysicalResources W
        then w W else 0 := by
  unfold markedPotentialLoad resourceRootOmittedLoad
  apply Finset.sum_congr rfl
  intro W _
  have hs : ∀ f∈markedOccurrenceResources W,
      Sum.elim (fun _ : E⊕K=>True) (fun vu=>H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2) f := by
    intro f hf
    cases f with
    | inl a => trivial
    | inr vu =>
      have hh := (markedOccurrenceResources_physical W (Sum.inr vu)).mp hf
      exact markedWheelPhysicalResources_spoke_present W vu.1 vu.2 hh
  have hs' : ∀ f∈markedOccurrenceResources W,f≠e →
      Sum.elim (fun _ : E⊕K=>True) (fun vu=>H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2) f :=
    fun f hf _=>hs f hf
  by_cases he : e∈markedOccurrenceResources W
  · rw [if_pos ⟨he,hs'⟩,if_pos ((markedOccurrenceResources_physical W e).mp he)]
  · rw [if_neg (fun h=>he h.1),if_neg (fun h=>he ((markedOccurrenceResources_physical W e).mpr h))]

theorem markedPotentialLoad_parent_rim
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K) :
    markedPotentialLoad w (fun _=>True) (fun v u=>H₀ v u ∨ Hₖ v u) (Sum.inl e)=markedWheelRimLoad w e := by
  rw [markedPotentialLoad_parent]
  exact markedWheelPhysicalResources_load_rim hp w e

theorem markedWheelPhysicalResources_load_typed_spoke
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (j : Bool) (v : V) (u : U) (he : if j then Hₖ v u else H₀ v u) :
    (∑ W,if Sum.inr (v,u)∈markedWheelPhysicalResources W then w W else 0)=markedWheelSpokeLoad w j v u := by
  rw [markedWheelPhysicalResources_load_spoke]
  cases j
  · have hn : ¬Hₖ v u := fun hk=>hdisj v u ⟨he,hk⟩
    have hz := markedWheelSpokeLoad_outside w true v u hn
    rw [hz,add_zero]
  · have hn : ¬H₀ v u := fun ho=>hdisj v u ⟨ho,he⟩
    have hz := markedWheelSpokeLoad_outside w false v u hn
    rw [hz,zero_add]

theorem markedPotentialLoad_parent_spoke
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (j : Bool) (v : V) (u : U) (he : if j then Hₖ v u else H₀ v u) :
    markedPotentialLoad w (fun _=>True) (fun v u=>H₀ v u ∨ Hₖ v u) (Sum.inr (v,u))=markedWheelSpokeLoad w j v u := by
  rw [markedPotentialLoad_parent]
  exact markedWheelPhysicalResources_load_typed_spoke hdisj w j v u he

theorem markedPotentialLoad_restricted_rim (PE : E → Prop) (PK : K → Prop)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (e : {e // PE e}⊕{e // PK e}) :
    markedPotentialLoad w (Sum.elim PE PK) (fun v u=>H₀' v u ∨ Hₖ' v u)
      (Sum.inl (Sum.map Subtype.val Subtype.val e))=
      markedWheelRimLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)) e := by
  have he : Sum.elim (Sum.elim PE PK) (fun vu : V×U=>H₀' vu.1 vu.2 ∨ Hₖ' vu.1 vu.2)
      (Sum.inl (Sum.map Subtype.val Subtype.val e)) := by
    cases e with
    | inl e => exact e.property
    | inr e => exact e.property
  have hh := markedPotentialLoad_restricted PE PK hp hH₀ hHₖ hdisj w
    (Sum.inl (Sum.map Subtype.val Subtype.val e)) he
  simp only [Sum.map_inl,← markedPhysicalEdge_restrict PE PK e] at hh
  exact hh.trans (markedWheelPhysicalResources_load_rim (markedPhysicalEdge_restrict_injective PE PK hp)
    (fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)) e)

theorem markedPotentialLoad_restricted_spoke (PE : E → Prop) (PK : K → Prop)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (j : Bool) (v : V) (u : U) (he : if j then Hₖ' v u else H₀' v u) :
    markedPotentialLoad w (Sum.elim PE PK) (fun v u=>H₀' v u ∨ Hₖ' v u) (Sum.inr (v,u))=
      markedWheelSpokeLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)) j v u := by
  have hroot : H₀' v u ∨ Hₖ' v u := by cases j;exact Or.inl he;exact Or.inr he
  have hd' : ∀ v u,¬(H₀' v u ∧ Hₖ' v u) := fun v u h=>hdisj v u ⟨hH₀ v u h.1,hHₖ v u h.2⟩
  have hh := markedPotentialLoad_restricted PE PK hp hH₀ hHₖ hdisj w (Sum.inr (v,u)) hroot
  simp only [Sum.map_inr,id_eq] at hh
  exact hh.trans (markedWheelPhysicalResources_load_typed_spoke hd'
    (fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)) j v u he)

/-- This is an identity of actual restricted rim loads, not only a bound
for an abstract potential. Each input loss counts realised occurrences. -/
theorem marked_restricted_rim_load_stability
    (hm : 3≤m) (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B d : ℝ) (hB : 0≤B) (hd : 0≤d)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (hout : ∀ x,(∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d)
    (hin : ∀ x,(∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d)
    (hHout : ∀ x,(∑ u,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤d)
    (hHin : ∀ u,(∑ x,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤d)
    (e : {e // PE e}⊕{e // PK e}) :
    |markedWheelRimLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)) e-
      markedWheelRimLoad w (Sum.map Subtype.val Subtype.val e)|≤8*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  have hsame (x : V) (u : U) : ¬((H₀ x u ∨ Hₖ x u)↔(H₀' x u ∨ Hₖ' x u)) ↔
      (H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u) := by
    have hsub : (H₀' x u ∨ Hₖ' x u) → (H₀ x u ∨ Hₖ x u) := Or.imp (hH₀ x u) (hHₖ x u)
    tauto
  have hh := markedPotentialLoad_rim_degree_stability hm hp hn hu w B hB hw
    (fun _=>True) (Sum.elim PE PK) (fun x u=>H₀ x u ∨ Hₖ x u) (fun x u=>H₀' x u ∨ Hₖ' x u) d hd
    (by intro x;convert hout x using 1 <;> simp only [true_iff] <;> congr!)
    (by intro x;convert hin x using 1 <;> simp only [true_iff] <;> congr!)
    (by intro x;convert hHout x using 1 <;> simp only [bipAdj,hsame] <;> congr!)
    (by intro u;convert hHin u using 1 <;> simp only [bipAdj,hsame] <;> congr!)
    (Sum.map Subtype.val Subtype.val e)
  rw [markedPotentialLoad_restricted_rim PE PK hp hH₀ hHₖ hdisj,
    markedPotentialLoad_parent_rim hp] at hh
  exact hh

theorem marked_restricted_spoke_load_stability
    (hm : 3≤m) (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B d : ℝ) (hB : 0≤B) (hd : 0≤d)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (hout : ∀ x,(∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d)
    (hin : ∀ x,(∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d)
    (hHout : ∀ x,(∑ u,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤d)
    (hHin : ∀ u,(∑ x,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤d)
    (j : Bool) (v : V) (u : U) (he : if j then Hₖ' v u else H₀' v u) :
    |markedWheelSpokeLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)) j v u-
      markedWheelSpokeLoad w j v u|≤4*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  have hsame (x : V) (a : U) : ¬((H₀ x a ∨ Hₖ x a)↔(H₀' x a ∨ Hₖ' x a)) ↔
      (H₀ x a ∨ Hₖ x a) ∧ ¬(H₀' x a ∨ Hₖ' x a) := by
    have hsub : (H₀' x a ∨ Hₖ' x a) → (H₀ x a ∨ Hₖ x a) := Or.imp (hH₀ x a) (hHₖ x a)
    tauto
  have hparent : if j then Hₖ v u else H₀ v u := by cases j;exact hH₀ v u he;exact hHₖ v u he
  have hh := markedPotentialLoad_spoke_degree_stability hm hp hn hu w B hB hw
    (fun _=>True) (Sum.elim PE PK) (fun x a=>H₀ x a ∨ Hₖ x a) (fun x a=>H₀' x a ∨ Hₖ' x a) d hd
    (by intro x;convert hout x using 1 <;> simp only [true_iff] <;> congr!)
    (by intro x;convert hin x using 1 <;> simp only [true_iff] <;> congr!)
    (by intro x;convert hHout x using 1 <;> simp only [bipAdj,hsame] <;> congr!)
    (by intro a;convert hHin a using 1 <;> simp only [bipAdj,hsame] <;> congr!) v u
  rw [markedPotentialLoad_restricted_spoke PE PK hp hH₀ hHₖ hdisj w j v u he,
    markedPotentialLoad_parent_spoke hdisj w j v u hparent] at hh
  exact hh

end Oberwolfach
