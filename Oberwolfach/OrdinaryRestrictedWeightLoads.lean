module

public import Oberwolfach.OrdinaryWheelRestriction

@[expose] public section
/-! Fixed parent wheel coefficients retain their bounds and approximate
loads after a bounded physical rim and spoke deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_restricted_weight_loads_from_parent
    (Q F D:SimpleGraph V) (H E:V→U→Prop) (r:ℕ) (hr:3≤r)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (bminus B d ε₀ εstar:ℝ)
    (hb:0<bminus) (hB:0≤B) (hd:0≤d)
    (hw:∀W,bminus/(Fintype.card V:ℝ)^(r-1)≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (hD:∀v,(D.degree v:ℝ)≤d)
    (hEout:∀v,(∑u,bipAdj E v u)≤d) (hEin:∀u,(∑v,bipAdj E v u)≤d)
    (hR:∀x y,Q.Adj x y→|ordinaryRimLoad w x y-1|≤ε₀)
    (hS:∀v u,H v u→|ordinarySpokeLoad w v u-1|≤ε₀)
    (hmargin:ε₀+8*(r:ℝ)^4*B*d/Fintype.card V≤εstar):
    ∃w':OrdinaryWheel (Q\D) F (fun v u=>H v u∧¬E v u) r→ℝ,
      (∀W,bminus/(Fintype.card V:ℝ)^(r-1)≤w' W ∧ w' W≤B/(Fintype.card V:ℝ)^(r-1)) ∧
      (∀x y,(Q\D).Adj x y→|ordinaryRimLoad w' x y-1|≤εstar) ∧
      (∀v u,H v u∧¬E v u→|ordinarySpokeLoad w' v u-1|≤εstar):=by
  let w':OrdinaryWheel (Q\D) F (fun v u=>H v u∧¬E v u) r→ℝ:=fun W=>
    w (ordinaryWheelToLarger (sdiff_le:Q\D≤Q) (fun v u h=>h.1) W)
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn
  have hw0:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1):=by
    intro W
    exact ⟨(div_nonneg hb.le (pow_nonneg hnR.le _)).trans (hw W).1,(hw W).2⟩
  have hsmall:4*(r:ℝ)^4*B*d/Fintype.card V≤8*(r:ℝ)^4*B*d/Fintype.card V:=by
    apply div_le_div_of_nonneg_right _ hnR.le
    have hh:0≤(r:ℝ)^4*B*d:=by positivity
    nlinarith only [hh]
  refine ⟨w',fun W=>hw _,?_,?_⟩
  · intro x y hxy
    have hs:=ordinary_restricted_rim_load_stability Q F D H E r (by omega) hn hu w B d hB hd hw0 hD hEout hEin x y hxy
    have hp:=hR x y hxy.1
    have ht:=abs_sub_le (ordinaryRimLoad w' x y) (ordinaryRimLoad w x y) 1
    change |ordinaryRimLoad w' x y-ordinaryRimLoad w x y|≤_ at hs
    linarith only [hs,hp,ht,hmargin]
  · intro v u hvu
    have hs:=ordinary_restricted_spoke_load_stability Q F D H E r (by omega) hn hu w B d hB hd hw0 hD hEout hEin v u hvu
    have hp:=hS v u hvu.1
    have ht:=abs_sub_le (ordinarySpokeLoad w' v u) (ordinarySpokeLoad w v u) 1
    change |ordinarySpokeLoad w' v u-ordinarySpokeLoad w v u|≤_ at hs
    linarith only [hs,hp,ht,hsmall,hmargin]
end Oberwolfach
