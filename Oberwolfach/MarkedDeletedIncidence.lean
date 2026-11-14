module

public import Oberwolfach.MarkedPackingTransport
public import Oberwolfach.TypedMatrixRealization

@[expose] public section

/-! Deleted incident-edge bounds in both representations of a marked host.
The physical marked indegree at v is the auxiliary indegree at π⁻¹(v). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem subtype_pair_filter_row {A B : Type*} [Fintype A] [Fintype B]
    (P Q : A → B → Prop) (a : A) :
    ((Finset.univ.filter (fun z : {z : A×B // P z.1 z.2}=>z.val.1=a ∧ Q z.val.1 z.val.2)).card:ℝ)=
      ∑ b,if P a b ∧ Q a b then (1:ℝ) else 0 := by
  have hh := finite_sum_restrict_of_zero (fun z : A×B=>P z.1 z.2)
    (fun z=>if P z.1 z.2 ∧ z.1=a ∧ Q z.1 z.2 then (1:ℝ) else 0)
    (by intro z hz;simp only [hz,false_and,ite_false])
  have he : (∑ z : {z : A×B // P z.1 z.2},if P z.val.1 z.val.2 ∧ z.val.1=a ∧ Q z.val.1 z.val.2 then (1:ℝ) else 0)=
      ∑ z : {z : A×B // P z.1 z.2},if z.val.1=a ∧ Q z.val.1 z.val.2 then (1:ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    simp only [z.property,true_and]
  rw [he] at hh
  rw [← Finset.sum_boole,← hh,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp only [true_and]
  · intro x _ hxa
    apply Finset.sum_eq_zero
    intro b _
    simp only [hxa,false_and,and_false,ite_false]
  · intro ha
    exact (ha (Finset.mem_univ _)).elim

theorem subtype_pair_filter_col {A B : Type*} [Fintype A] [Fintype B]
    (P Q : A → B → Prop) (b : B) :
    ((Finset.univ.filter (fun z : {z : A×B // P z.1 z.2}=>z.val.2=b ∧ Q z.val.1 z.val.2)).card:ℝ)=
      ∑ a,if P a b ∧ Q a b then (1:ℝ) else 0 := by
  let e : {z : A×B // P z.1 z.2} ≃ {z : B×A // P z.2 z.1} :=
    { toFun:=fun z=>⟨z.val.swap,z.property⟩
      invFun:=fun z=>⟨z.val.swap,z.property⟩
      left_inv:=fun z=>by rfl
      right_inv:=fun z=>by rfl }
  have hh := subtype_pair_filter_row (fun b a=>P a b) (fun b a=>Q a b) b
  rw [← Finset.sum_boole] at hh ⊢
  rw [← e.sum_comp] at hh
  exact hh

theorem deleted_occurrence_incidence_le {A V : Type*} [Fintype A]
    (f g : A → V) (P : A → Prop) (v : V) (d : ℝ)
    (hf : (∑ e,if ¬P e ∧ f e=v then (1:ℝ) else 0)≤d)
    (hg : (∑ e,if ¬P e ∧ g e=v then (1:ℝ) else 0)≤d) :
    ((Finset.univ.filter (fun e=>(f e=v ∨ g e=v) ∧ ¬P e)).card:ℝ)≤2*d := by
  rw [← Finset.sum_boole]
  calc
    _ ≤ ∑ e,((if ¬P e ∧ f e=v then (1:ℝ) else 0)+(if ¬P e ∧ g e=v then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hp : P e <;> by_cases hfe : f e=v <;> by_cases hge : g e=v <;> simp [hp,hfe,hge]
    _ ≤ 2*d := by rw [Finset.sum_add_distrib];linarith only [hf,hg]

theorem deleted_spoke_union_row_le {V U : Type*} [Fintype V] [Fintype U]
    (H₀ Hₖ H₀' Hₖ' : V → U → Prop) (v : V) (d : ℝ)
    (h0 : (∑ u,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hk : (∑ u,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d) :
    ((Finset.univ.filter (fun z : {z : V×U // H₀ z.1 z.2 ∨ Hₖ z.1 z.2}=>
      z.val.1=v ∧ ¬(H₀' z.val.1 z.val.2 ∨ Hₖ' z.val.1 z.val.2))).card:ℝ)≤2*d := by
  have he := subtype_pair_filter_row (fun v u=>H₀ v u ∨ Hₖ v u) (fun v u=>¬(H₀' v u ∨ Hₖ' v u)) v
  have he' : ((Finset.univ.filter (fun z : {z : V×U // H₀ z.1 z.2 ∨ Hₖ z.1 z.2}=>
      z.val.1=v ∧ ¬(H₀' z.val.1 z.val.2 ∨ Hₖ' z.val.1 z.val.2))).card:ℝ)=
      ∑ u,if (H₀ v u ∨ Hₖ v u) ∧ ¬(H₀' v u ∨ Hₖ' v u) then (1:ℝ) else 0 := by
    convert he using 1 <;> congr!
  rw [he']
  calc
    _ ≤ ∑ u,((if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)+(if Hₖ v u ∧ ¬Hₖ' v u then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro u _
      by_cases h0 : H₀ v u <;> by_cases hk : Hₖ v u <;>
        by_cases h0' : H₀' v u <;> by_cases hk' : Hₖ' v u <;> simp [h0,hk,h0',hk']
    _ ≤ 2*d := by rw [Finset.sum_add_distrib];linarith only [h0,hk]

theorem deleted_spoke_union_col_le {V U : Type*} [Fintype V] [Fintype U]
    (H₀ Hₖ H₀' Hₖ' : V → U → Prop) (u : U) (d : ℝ)
    (h0 : (∑ v,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hk : (∑ v,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d) :
    ((Finset.univ.filter (fun z : {z : V×U // H₀ z.1 z.2 ∨ Hₖ z.1 z.2}=>
      z.val.2=u ∧ ¬(H₀' z.val.1 z.val.2 ∨ Hₖ' z.val.1 z.val.2))).card:ℝ)≤2*d := by
  have he := subtype_pair_filter_col (fun v u=>H₀ v u ∨ Hₖ v u) (fun v u=>¬(H₀' v u ∨ Hₖ' v u)) u
  have he' : ((Finset.univ.filter (fun z : {z : V×U // H₀ z.1 z.2 ∨ Hₖ z.1 z.2}=>
      z.val.2=u ∧ ¬(H₀' z.val.1 z.val.2 ∨ Hₖ' z.val.1 z.val.2))).card:ℝ)=
      ∑ v,if (H₀ v u ∨ Hₖ v u) ∧ ¬(H₀' v u ∨ Hₖ' v u) then (1:ℝ) else 0 := by
    convert he using 1 <;> congr!
  rw [he']
  calc
    _ ≤ ∑ v,((if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)+(if Hₖ v u ∧ ¬Hₖ' v u then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases h0 : H₀ v u <;> by_cases hk : Hₖ v u <;>
        by_cases h0' : H₀' v u <;> by_cases hk' : Hₖ' v u <;> simp [h0,hk,h0',hk']
    _ ≤ 2*d := by rw [Finset.sum_add_distrib];linarith only [h0,hk]

theorem deleted_spoke_union_row_sum_le {V U : Type*} [Fintype V] [Fintype U]
    (H₀ Hₖ H₀' Hₖ' : V → U → Prop) (v : V) (d : ℝ)
    (h0 : (∑ u,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hk : (∑ u,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d) :
    (∑ u,if (H₀ v u ∨ Hₖ v u) ∧ ¬(H₀' v u ∨ Hₖ' v u) then (1:ℝ) else 0)≤2*d := by
  have hh := deleted_spoke_union_row_le H₀ Hₖ H₀' Hₖ' v d h0 hk
  have he := subtype_pair_filter_row (fun v u=>H₀ v u ∨ Hₖ v u) (fun v u=>¬(H₀' v u ∨ Hₖ' v u)) v
  have he' : ((Finset.univ.filter (fun z : {z : V×U // H₀ z.1 z.2 ∨ Hₖ z.1 z.2}=>
      z.val.1=v ∧ ¬(H₀' z.val.1 z.val.2 ∨ Hₖ' z.val.1 z.val.2))).card:ℝ)=
      ∑ u,if (H₀ v u ∨ Hₖ v u) ∧ ¬(H₀' v u ∨ Hₖ' v u) then (1:ℝ) else 0 := by
    convert he using 1 <;> congr!
  rw [he'] at hh
  exact hh

theorem deleted_spoke_union_col_sum_le {V U : Type*} [Fintype V] [Fintype U]
    (H₀ Hₖ H₀' Hₖ' : V → U → Prop) (u : U) (d : ℝ)
    (h0 : (∑ v,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hk : (∑ v,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d) :
    (∑ v,if (H₀ v u ∨ Hₖ v u) ∧ ¬(H₀' v u ∨ Hₖ' v u) then (1:ℝ) else 0)≤2*d := by
  have hh := deleted_spoke_union_col_le H₀ Hₖ H₀' Hₖ' u d h0 hk
  have he := subtype_pair_filter_col (fun v u=>H₀ v u ∨ Hₖ v u) (fun v u=>¬(H₀' v u ∨ Hₖ' v u)) u
  have he' : ((Finset.univ.filter (fun z : {z : V×U // H₀ z.1 z.2 ∨ Hₖ z.1 z.2}=>
      z.val.2=u ∧ ¬(H₀' z.val.1 z.val.2 ∨ Hₖ' z.val.1 z.val.2))).card:ℝ)=
      ∑ v,if (H₀ v u ∨ Hₖ v u) ∧ ¬(H₀' v u ∨ Hₖ' v u) then (1:ℝ) else 0 := by
    convert he using 1 <;> congr!
  rw [he'] at hh
  exact hh

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem marked_deleted_incidence_bound (tail head : E → V) (ktail khead : K → V)
    (π : Equiv.Perm V) (H₀ Hₖ H₀' Hₖ' : V → U → Prop) (PE : E → Prop) (PK : K → Prop)
    (d : ℝ) (hd : 0≤d)
    (hEout : ∀ v,(∑ e,if ¬PE e ∧ tail e=v then (1:ℝ) else 0)≤d)
    (hEin : ∀ v,(∑ e,if ¬PE e ∧ head e=v then (1:ℝ) else 0)≤d)
    (hKout : ∀ v,(∑ e,if ¬PK e ∧ ktail e=v then (1:ℝ) else 0)≤d)
    (hKin : ∀ v,(∑ e,if ¬PK e ∧ khead e=v then (1:ℝ) else 0)≤d)
    (hH0row : ∀ v,(∑ u,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hHKrow : ∀ v,(∑ u,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d)
    (hH0col : ∀ u,(∑ v,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hHKcol : ∀ u,(∑ v,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d)
    (physical : Bool) (x : V⊕U) :
    (((markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x).filter
      (fun e=>¬markedActiveRetained PE PK H₀' Hₖ' e)).card:ℝ)≤6*d := by
  have hK (v : V) : (∑ e,if ¬PK e ∧ (if physical then π (khead e) else khead e)=v then (1:ℝ) else 0)≤d := by
    cases physical with
    | false => exact hKin v
    | true =>
      convert hKin (π.symm v) using 1
      apply Finset.sum_congr rfl
      intro e _
      simp only [ite_true,Equiv.apply_eq_iff_eq_symm_apply]
  unfold markedIncidentEdges
  simp only [Finset.filter_filter,← Finset.sum_boole,Fintype.sum_sum_type]
  cases x with
  | inl v =>
    simp only [markedResourceIncident,markedActiveRetained]
    have hE := deleted_occurrence_incidence_le tail head PE v d (by convert hEout v using 1 <;> congr!) (by convert hEin v using 1 <;> congr!)
    have hK' := deleted_occurrence_incidence_le ktail (fun e=>if physical then π (khead e) else khead e) PK v d (by convert hKout v using 1 <;> congr!) (by convert hK v using 1 <;> congr!)
    have hS := deleted_spoke_union_row_le H₀ Hₖ H₀' Hₖ' v d (hH0row v) (hHKrow v)
    simp only [← Finset.sum_boole] at hE hK' hS
    have hh := add_le_add (add_le_add hE hK') hS
    convert (hh.trans (by linarith : 2*d+2*d+2*d≤6*d)) using 1 <;> congr!
  | inr u =>
    simp only [markedResourceIncident,false_and,ite_false,Finset.sum_const_zero,
      zero_add,markedActiveRetained]
    have hh := deleted_spoke_union_col_le H₀ Hₖ H₀' Hₖ' u d (hH0col u) (hHKcol u)
    simp only [← Finset.sum_boole] at hh
    convert (hh.trans (by linarith : 2*d≤6*d)) using 1 <;> congr!

theorem marked_packing_transport_bounds
    {tail head : E → V} {ktail khead : K → V} {π : Equiv.Perm V} {m b : ℕ}
    {H₀ Hₖ H₀' Hₖ' : V → U → Prop}
    (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M : Finset (MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ'))
    (hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (a d : ℝ) (hd : 0≤d)
    (haux : ∀ x : V⊕U,((markedIncidentEdges (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' false x \
      M.biUnion markedActiveResources).card:ℝ)≤a)
    (hphys : ∀ x : V⊕U,((markedPhysicalIncidentEdges (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' x \
      M.biUnion markedWheelPhysicalResources).card:ℝ)≤a)
    (hEout : ∀ v,(∑ e,if ¬PE e ∧ tail e=v then (1:ℝ) else 0)≤d)
    (hEin : ∀ v,(∑ e,if ¬PE e ∧ head e=v then (1:ℝ) else 0)≤d)
    (hKout : ∀ v,(∑ e,if ¬PK e ∧ ktail e=v then (1:ℝ) else 0)≤d)
    (hKin : ∀ v,(∑ e,if ¬PK e ∧ khead e=v then (1:ℝ) else 0)≤d)
    (hH0row : ∀ v,(∑ u,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hHKrow : ∀ v,(∑ u,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d)
    (hH0col : ∀ u,(∑ v,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hHKcol : ∀ u,(∑ v,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d) :
    let M' := M.image (markedWheelToLarger PE PK hH₀ hHₖ)
    (∀ W∈M',∀ Z∈M',W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
    (∀ x : V⊕U,((markedIncidentEdges tail head ktail khead π H₀ Hₖ false x \
      M'.biUnion markedActiveResources).card:ℝ)≤a+6*d) ∧
    (∀ x : V⊕U,((markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x \
      M'.biUnion markedWheelPhysicalResources).card:ℝ)≤a+6*d) := by
  let M' := M.image (markedWheelToLarger PE PK hH₀ hHₖ)
  have hactive (physical : Bool) (x : V⊕U) :
      ((markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x \
        M'.biUnion markedActiveResources).card:ℝ)≤a+6*d := by
    have ht := marked_leftover_transport PE PK hH₀ hHₖ hp M physical x
    have hdel := marked_deleted_incidence_bound tail head ktail khead π H₀ Hₖ H₀' Hₖ' PE PK d hd
      hEout hEin hKout hKin hH0row hHKrow hH0col hHKcol physical x
    have hsmall : ((markedIncidentEdges (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' physical x \
        M.biUnion markedActiveResources).card:ℝ)≤a := by
      cases physical with
      | false => exact haux x
      | true =>
        have he := marked_leftover_card_physical
          (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
          (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ'
          (markedRestrictedPhysical_injective PE PK hp) M x
        have hh := hphys x
        rw [← he] at hh
        convert hh using 1 <;> congr!
    have ht' := (Nat.cast_le (α:=ℝ)).mpr ht
    simp only [Nat.cast_add] at ht'
    change _≤a+6*d
    linarith
  refine ⟨markedWheelToLarger_matching PE PK hH₀ hHₖ M hM,hactive false,?_⟩
  intro x
  have hh := hactive true x
  rw [marked_leftover_card_physical _ _ _ _ _ _ _ hp] at hh
  exact hh

end Oberwolfach
