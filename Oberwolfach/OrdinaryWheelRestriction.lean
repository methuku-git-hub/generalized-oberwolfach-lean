module

public import Oberwolfach.OrdinaryActiveResources
public import Oberwolfach.OrdinaryCycleWeightRestriction
public import Oberwolfach.OrdinaryPotentialDegreeStability

@[expose] public section

/-! Restricting fixed wheel weights to a smaller host. The physical rim,
hub and coefficients are retained, without choosing new representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {P Q F : SimpleGraph V} {Hbase H : V → U → Prop} {r : ℕ}

def ordinaryWheelToLarger (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u)
    (W : OrdinaryWheel Q F H r) : OrdinaryWheel P F Hbase r :=
  ⟨(⟨W.val.1.val,W.val.1.property.trans hQ⟩,W.val.2),
    fun v hv=>hH v W.val.2 (W.property.1 v hv),W.property.2⟩

theorem ordinaryWheelToLarger_resources (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u)
    (W : OrdinaryWheel Q F H r) :
    ordinaryWheelResources (ordinaryWheelToLarger hQ hH W)=ordinaryWheelResources W := rfl

theorem ordinaryWheelToLarger_injective (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u) :
    Function.Injective (ordinaryWheelToLarger (F:=F) (r:=r) hQ hH) := by
  intro W Z he
  apply ordinaryWheelResources_injective
  have hh := congrArg (fun T : OrdinaryWheel P F Hbase r=>ordinaryWheelResources T) he
  simpa only [ordinaryWheelToLarger_resources] using hh

def OrdinaryWheelSurvives (W : OrdinaryWheel P F Hbase r)
    (Q : SimpleGraph V) (H : V → U → Prop) : Prop :=
  ordinaryWheelRim W≤Q ∧ ∀ v∈(ordinaryWheelRim W).support,H v (ordinaryWheelHub W)

def ordinaryWheelRestrictionEquiv (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u) :
    {W : OrdinaryWheel P F Hbase r // OrdinaryWheelSurvives W Q H} ≃ OrdinaryWheel Q F H r where
  toFun W := ⟨(⟨W.val.val.1.val,W.property.1⟩,W.val.val.2),W.property.2,W.val.property.2⟩
  invFun W := ⟨ordinaryWheelToLarger hQ hH W,W.val.1.property,W.property.1⟩
  left_inv W := by rfl
  right_inv W := by rfl

theorem ordinaryWheelSurvives_iff_resources (W : OrdinaryWheel P F Hbase r) :
    OrdinaryWheelSurvives W Q H ↔ ∀ e∈ordinaryWheelResources W,ordinaryResourceState Q H e=true := by
  constructor
  · intro h e he
    cases e with
    | inl e =>
      rw [ordinaryWheelResources_rim] at he
      have hh := SimpleGraph.edgeSet_mono h.1 he
      simpa only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq] using hh
    | inr vu =>
      rw [ordinaryWheelResources_spoke] at he
      have hh := h.2 vu.1 he.2
      rw [he.1] at hh
      simpa only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq] using hh
  · intro h
    constructor
    · intro x y hxy
      have he : Sum.inl s(x,y)∈ordinaryWheelResources W :=
        (ordinaryWheelResources_rim W s(x,y)).mpr hxy
      have hh := h _ he
      simpa only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq,SimpleGraph.mem_edgeSet] using hh
    · intro v hv
      have he : Sum.inr (v,ordinaryWheelHub W)∈ordinaryWheelResources W :=
        (ordinaryWheelResources_spoke W v _).mpr ⟨rfl,hv⟩
      have hh := h _ he
      simpa only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq] using hh

theorem ordinary_wheel_restricted_resource_load (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u)
    (w : OrdinaryWheel P F Hbase r → ℝ) (e : Sym2 V⊕(V×U)) :
    (∑ W : OrdinaryWheel Q F H r,if e∈ordinaryWheelResources W then w (ordinaryWheelToLarger hQ hH W) else 0)=
      ∑ W : OrdinaryWheel P F Hbase r,if e∈ordinaryWheelResources W ∧ OrdinaryWheelSurvives W Q H then w W else 0 := by
  let f (W : OrdinaryWheel P F Hbase r) := if e∈ordinaryWheelResources W ∧ OrdinaryWheelSurvives W Q H then w W else 0
  have he := finite_sum_restrict_of_zero (fun W=>OrdinaryWheelSurvives W Q H) f
    (by intro W hW;simp only [f,hW,and_false,ite_false])
  rw [he]
  have hh := (ordinaryWheelRestrictionEquiv (F:=F) (r:=r) hQ hH).sum_comp
    (fun W : OrdinaryWheel Q F H r=>if e∈ordinaryWheelResources W then w (ordinaryWheelToLarger hQ hH W) else 0)
  rw [← hh]
  apply Finset.sum_congr rfl
  intro W _
  have hw : ordinaryWheelToLarger hQ hH ((ordinaryWheelRestrictionEquiv hQ hH) W)=W.val := rfl
  have hr : ordinaryWheelResources ((ordinaryWheelRestrictionEquiv hQ hH) W)=ordinaryWheelResources W.val := rfl
  rw [hw,hr]
  dsimp only [f]
  simp only [W.property,and_true]


/-- At a present root, the potential load is exactly the physical load of
the restricted weighting. The coefficients are composed with the fixed inclusion. -/
theorem ordinaryPotentialLoad_restriction (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u)
    (w : OrdinaryWheel P F Hbase r → ℝ) (e : Sym2 V⊕(V×U))
    (he : ordinaryResourceState Q H e=true) :
    ordinaryPotentialLoad w e Q H=
      ∑ W : OrdinaryWheel Q F H r,if e∈ordinaryWheelResources W then w (ordinaryWheelToLarger hQ hH W) else 0 := by
  rw [ordinaryPotentialLoad_present w e Q H he]
  simp_rw [← ordinaryWheelSurvives_iff_resources]
  exact (ordinary_wheel_restricted_resource_load hQ hH w e).symm

theorem ordinaryPotentialLoad_full (w : OrdinaryWheel P F Hbase r → ℝ)
    (e : Sym2 V⊕(V×U)) :
    ordinaryPotentialLoad w e P Hbase=∑ W,if e∈ordinaryWheelResources W then w W else 0 := by
  unfold ordinaryPotentialLoad
  apply Finset.sum_congr rfl
  intro W _
  rw [patternValue_indicator]
  have hh : ∀ f∈ordinaryWheelResources W\{e},ordinaryResourceState P Hbase f=true := by
    intro f hf
    exact ordinaryWheelResources_present W f (Finset.mem_sdiff.mp hf).1
  rw [if_pos hh,mul_one]

theorem ordinaryPotentialLoad_restriction_rim (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u)
    (w : OrdinaryWheel P F Hbase r → ℝ) (x y : V) (hxy : Q.Adj x y) :
    ordinaryPotentialLoad w (Sum.inl s(x,y)) Q H=
      ordinaryRimLoad (fun W=>w (ordinaryWheelToLarger hQ hH W)) x y := by
  rw [ordinaryPotentialLoad_restriction hQ hH w _ (by
    simpa only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq,SimpleGraph.mem_edgeSet] using hxy)]
  exact ordinaryWheelResources_load_rim _ x y

theorem ordinaryPotentialLoad_restriction_spoke (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u)
    (w : OrdinaryWheel P F Hbase r → ℝ) (v : V) (u : U) (hvu : H v u) :
    ordinaryPotentialLoad w (Sum.inr (v,u)) Q H=
      ordinarySpokeLoad (fun W=>w (ordinaryWheelToLarger hQ hH W)) v u := by
  rw [ordinaryPotentialLoad_restriction hQ hH w _ (by
    simpa only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq] using hvu)]
  exact ordinaryWheelResources_load_spoke _ v u


theorem graph_deletion_change_degree (Q D : SimpleGraph V) (d : ℝ)
    (hD : ∀ v,(D.degree v : ℝ)≤d) (v : V) :
    (∑ z,bipAdj (fun x y=>¬(Q.Adj x y↔(Q\D).Adj x y)) v z)≤d := by
  have he : (D.degree v : ℝ)=∑ z,bipAdj D.Adj v z := by
    rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro z _
    dsimp [bipAdj]
  apply le_trans ?_ (hD v)
  rw [he]
  apply Finset.sum_le_sum
  intro z _
  dsimp [bipAdj]
  simp only [SimpleGraph.sdiff_adj]
  split_ifs <;> norm_num <;> tauto

theorem relation_deletion_change_row (H E : V → U → Prop) (d : ℝ)
    (hE : ∀ v,(∑ u,bipAdj E v u)≤d) (v : V) :
    (∑ u,bipAdj (fun v u=>¬(H v u↔H v u ∧ ¬E v u)) v u)≤d := by
  apply le_trans ?_ (hE v)
  apply Finset.sum_le_sum
  intro u _
  dsimp [bipAdj]
  split_ifs <;> norm_num <;> tauto

theorem relation_deletion_change_column (H E : V → U → Prop) (d : ℝ)
    (hE : ∀ u,(∑ v,bipAdj E v u)≤d) (u : U) :
    (∑ v,bipAdj (fun v u=>¬(H v u↔H v u ∧ ¬E v u)) v u)≤d := by
  apply le_trans ?_ (hE u)
  apply Finset.sum_le_sum
  intro v _
  dsimp [bipAdj]
  split_ifs <;> norm_num <;> tauto

/-- The original seed coefficients are restricted to surviving physical
wheels; their rim loads change by the degree-controlled potential estimate. -/
theorem ordinary_restricted_rim_load_stability
    (Q F D : SimpleGraph V) (H E : V → U → Prop) (r : ℕ) (hr : 2≤r)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel Q F H r → ℝ) (B d : ℝ) (hB : 0≤B) (hd : 0≤d)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V : ℝ)^(r-1))
    (hD : ∀ v,(D.degree v : ℝ)≤d)
    (hEout : ∀ v,(∑ u,bipAdj E v u)≤d) (hEin : ∀ u,(∑ v,bipAdj E v u)≤d)
    (x y : V) (hxy : (Q\D).Adj x y) :
    |ordinaryRimLoad (fun W=>w (ordinaryWheelToLarger (sdiff_le : Q\D≤Q)
       (fun v u (h : H v u ∧ ¬E v u)=>h.1) W)) x y-ordinaryRimLoad w x y|≤
      8*(r : ℝ)^4*B*d/Fintype.card V := by
  have hh := ordinaryPotentialLoad_rim_degree_stability Q F H r hr hn hu w B hB hw
    Q (Q\D) H (fun v u=>H v u ∧ ¬E v u) d hd
    (graph_deletion_change_degree Q D d hD)
    (relation_deletion_change_row H E d hEout)
    (relation_deletion_change_column H E d hEin) x y hxy.ne
  rw [ordinaryPotentialLoad_restriction_rim (sdiff_le : Q\D≤Q) (fun v u (h : H v u ∧ ¬E v u)=>h.1) w x y hxy,
    ordinaryPotentialLoad_full,ordinaryWheelResources_load_rim] at hh
  exact hh

theorem ordinary_restricted_spoke_load_stability
    (Q F D : SimpleGraph V) (H E : V → U → Prop) (r : ℕ) (hr : 2≤r)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel Q F H r → ℝ) (B d : ℝ) (hB : 0≤B) (hd : 0≤d)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V : ℝ)^(r-1))
    (hD : ∀ v,(D.degree v : ℝ)≤d)
    (hEout : ∀ v,(∑ u,bipAdj E v u)≤d) (hEin : ∀ u,(∑ v,bipAdj E v u)≤d)
    (v : V) (u : U) (hvu : H v u ∧ ¬E v u) :
    |ordinarySpokeLoad (fun W=>w (ordinaryWheelToLarger (sdiff_le : Q\D≤Q)
       (fun v u (h : H v u ∧ ¬E v u)=>h.1) W)) v u-ordinarySpokeLoad w v u|≤
      4*(r : ℝ)^4*B*d/Fintype.card V := by
  have hh := ordinaryPotentialLoad_spoke_degree_stability Q F H r hr hn hu w B hB hw
    Q (Q\D) H (fun v u=>H v u ∧ ¬E v u) d hd
    (graph_deletion_change_degree Q D d hD)
    (relation_deletion_change_row H E d hEout)
    (relation_deletion_change_column H E d hEin) v u
  rw [ordinaryPotentialLoad_restriction_spoke (sdiff_le : Q\D≤Q) (fun v u (h : H v u ∧ ¬E v u)=>h.1) w v u hvu,
    ordinaryPotentialLoad_full,ordinaryWheelResources_load_spoke] at hh
  exact hh

end Oberwolfach
