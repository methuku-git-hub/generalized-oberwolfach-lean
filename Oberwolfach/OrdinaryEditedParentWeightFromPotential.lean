module

public import Oberwolfach.OrdinaryPotentialDegreeStability
public import Oberwolfach.OrdinaryWheelRestriction

@[expose] public section
/-! Fixed ambient weights give actual parent-wheel weights after bounded
symmetric rim and spoke edits, using the original potential-load estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edited_parent_weight_from_potential
    (P Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (r:ℕ) (hr:2≤r)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel P F (fun _ _=>True) r→ℝ) (b B ε₀ εstar d:ℝ)
    (hb:0≤b) (hB:0≤B) (hd:0≤d) (hQP:Q≤P)
    (hw:∀W,b/(Fintype.card V:ℝ)^(r-1)≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (hQ:∀x,(∑y,bipAdj (fun x y=>¬(Q₀.Adj x y↔Q.Adj x y)) x y)≤d)
    (hHout:∀x,(∑u,bipAdj (fun x u=>¬(H₀ x u↔H x u)) x u)≤d)
    (hHin:∀u,(∑x,bipAdj (fun x u=>¬(H₀ x u↔H x u)) x u)≤d)
    (hR:∀x y,Q.Adj x y→|ordinaryPotentialLoad w (Sum.inl s(x,y)) Q₀ H₀-1|≤ε₀)
    (hS:∀v u,H v u→|ordinaryPotentialLoad w (Sum.inr (v,u)) Q₀ H₀-1|≤ε₀)
    (hmargin:ε₀+8*(r:ℝ)^4*B*d/Fintype.card V≤εstar):
    ∃w':OrdinaryWheel Q F H r→ℝ,
      (∀W,b/(Fintype.card V:ℝ)^(r-1)≤w' W ∧ w' W≤B/(Fintype.card V:ℝ)^(r-1)) ∧
      (∀x y,Q.Adj x y→|ordinaryRimLoad w' x y-1|≤εstar) ∧
      (∀v u,H v u→|ordinarySpokeLoad w' v u-1|≤εstar):=by
  let w':OrdinaryWheel Q F H r→ℝ:=fun W=>w (ordinaryWheelToLarger hQP (fun _ _ _=>trivial) W)
  have hnonneg:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1):=by
    intro W
    exact ⟨(div_nonneg hb (by positivity)).trans (hw W).1,(hw W).2⟩
  refine ⟨w',fun W=>hw _,?_,?_⟩
  · intro x y hxy
    have hst:=ordinaryPotentialLoad_rim_degree_stability P F (fun _ _=>True) r hr hn hu w B hB hnonneg
      Q₀ Q H₀ H d hd hQ hHout hHin x y hxy.ne
    have he:=ordinaryPotentialLoad_restriction_rim (H:=H) hQP (fun _ _ _=>trivial) w x y hxy
    have ht:=abs_sub_le (ordinaryRimLoad w' x y) (ordinaryPotentialLoad w (Sum.inl s(x,y)) Q₀ H₀) 1
    have hst':|ordinaryRimLoad w' x y-ordinaryPotentialLoad w (Sum.inl s(x,y)) Q₀ H₀|≤
        8*(r:ℝ)^4*B*d/Fintype.card V:=by rw [←he];exact hst
    exact ht.trans ((add_le_add hst' (hR x y hxy)).trans (by linarith only [hmargin]))
  · intro v u hvu
    have hst:=ordinaryPotentialLoad_spoke_degree_stability P F (fun _ _=>True) r hr hn hu w B hB hnonneg
      Q₀ Q H₀ H d hd hQ hHout hHin v u
    have he:=ordinaryPotentialLoad_restriction_spoke (H:=H) hQP (fun _ _ _=>trivial) w v u hvu
    have ht:=abs_sub_le (ordinarySpokeLoad w' v u) (ordinaryPotentialLoad w (Sum.inr (v,u)) Q₀ H₀) 1
    have hst':|ordinarySpokeLoad w' v u-ordinaryPotentialLoad w (Sum.inr (v,u)) Q₀ H₀|≤
        4*(r:ℝ)^4*B*d/Fintype.card V:=by rw [←he];exact hst
    have hmul:4*(r:ℝ)^4*B*d≤8*(r:ℝ)^4*B*d:=by
      have hpos:0≤(r:ℝ)^4*B*d:=by positivity
      nlinarith only [hpos]
    have hcompare:=div_le_div_of_nonneg_right hmul (Nat.cast_nonneg (Fintype.card V): (0:ℝ)≤_)
    exact ht.trans ((add_le_add hst' (hS v u hvu)).trans (by linarith only [hmargin,hcompare]))
end Oberwolfach
