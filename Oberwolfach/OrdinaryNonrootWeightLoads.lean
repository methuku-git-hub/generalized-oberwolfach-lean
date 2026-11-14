module

public import Oberwolfach.OrdinaryNonrootWeightRimIdentity
public import Oberwolfach.OrdinaryNonrootWeightSpokeIdentity
public import Oberwolfach.OrdinaryNonrootRimWheelLoadLoss
public import Oberwolfach.OrdinaryNonrootSpokeWheelLoadLoss

@[expose] public section
/-! The original positive wheel weights retain their rim and spoke load
estimates after removing the adaptive root domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_weight_loads (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B ε:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (hR:∀x y,Q.Adj x y→|ordinaryRimLoad w x y-1|≤ε)
    (hS:∀v u,H v u→|ordinarySpokeLoad w v u-1|≤ε)
    (T:Finset V) (W:Finset U):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let w':=ordinaryInducedWheelWeight Q F H A C r w;
    (∀x y:A,(Q.induce (A:Set V)).Adj x y→|ordinaryRimLoad w' x y-1|≤
      ε+((T.card:ℝ)+W.card)*((r:ℝ)^4*B/Fintype.card V)) ∧
    (∀(v:A) (u:C),H v.val u.val→|ordinarySpokeLoad w' v u-1|≤
      ε+((T.card:ℝ)+W.card)*((r:ℝ)^4*B/Fintype.card V)):=by
  intro A C w'
  have hL:(0:ℝ)≤(r:ℝ)^4*B/Fintype.card V:=by positivity
  constructor
  · intro x y hxy
    have hx:x.val∉T:=(Finset.mem_sdiff.mp x.property).2
    have hy:y.val∉T:=(Finset.mem_sdiff.mp y.property).2
    have hxy':x.val≠y.val:=by intro hh;exact hxy.ne (Subtype.ext hh)
    have he:=ordinary_nonroot_weight_rim_identity Q F H r T W w x y
    have hb:=ordinary_rim_nonroot_wheel_load_loss Q F H r hr hn hu w B hB hw T W x.val y.val hxy' hx hy
    have hb0:(0:ℝ)≤∑ D,if (ordinaryWheelRim D).Adj x.val y.val ∧
      (ordinaryWheelHub D∈W ∨ ∃z∈T,z∈(ordinaryWheelRim D).support) then w D else 0:=by
      apply Finset.sum_nonneg;intro D _;split_ifs <;> simp_all [(hw D).1]
    have hp:=abs_le.mp (hR x.val y.val hxy)
    apply abs_le.mpr
    constructor <;> linarith
  · intro v u huv
    have hv:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
    have hu':u.val∉W:=(Finset.mem_sdiff.mp u.property).2
    have he:=ordinary_nonroot_weight_spoke_identity Q F H r T W w v u
    have hb:=ordinary_spoke_nonroot_wheel_load_loss Q F H r hr hn hu w B hB hw T W v.val u.val hv hu'
    have hb0:(0:ℝ)≤∑ D,if (ordinaryWheelHub D=u.val ∧ v.val∈(ordinaryWheelRim D).support) ∧
      (ordinaryWheelHub D∈W ∨ ∃z∈T,z∈(ordinaryWheelRim D).support) then w D else 0:=by
      apply Finset.sum_nonneg;intro D _;split_ifs <;> simp_all [(hw D).1]
    have hmargin:(T.card:ℝ)*((r:ℝ)^4*B/Fintype.card V)≤
        ((T.card:ℝ)+W.card)*((r:ℝ)^4*B/Fintype.card V):=by nlinarith [Nat.cast_nonneg (α:=ℝ) W.card]
    have hp:=abs_le.mp (hS v.val u.val huv)
    apply abs_le.mpr
    constructor <;> linarith
end Oberwolfach
