module

public import Oberwolfach.OrientationRouting
public import Oberwolfach.BalancedOrientation

@[expose] public section
/-! Balance a regular class graph using directed two-path routing. The class
graph may have much smaller degree than the original dense host. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_orientation_routing
    {V:Type} [Fintype V] [DecidableEq V]
    (S E Protected:SimpleGraph V) (M₀:V→V→ℕ) (m L:ℕ)
    (hregular:S.IsRegularOfDegree (2*m)) (hL:0<L) (hn:0<Fintype.card V)
    (a f β:ℝ) (ha:0≤a) (hf:0≤f) (hβ:0<β)
    (hphysical:∀x y,M₀ x y+M₀ y x=if S.Adj x y then 1 else 0)
    (herr:∀v,|((∑w,M₀ v w:ℕ):ℝ)-m|≤a)
    (hforbid:∀v,(Protected.degree v:ℝ)≤f)
    (hpaths:∀x y,x≠y→β*Fintype.card V≤
      ((Finset.univ.filter (fun z=>0<M₀ x z ∧ 0<M₀ z y ∧ E.Adj x z ∧ E.Adj z y)).card:ℝ))
    (hmargin:(Fintype.card V:ℝ)*a/L+2*a+4*L+2*f<β*Fintype.card V):
    ∃M:V→V→ℕ,
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m) ∧
      (∀x y,M x y≠M₀ x y ∨ M y x≠M₀ y x→E.Adj x y ∧ ¬Protected.Adj x y) ∧
      (∀v,((Finset.univ.filter (fun w=>M v w≠M₀ v w ∨ M w v≠M₀ w v)).card:ℝ)≤a+2*L):=by
  have htotal:(∑_v:V,m)=S.edgeFinset.card:=by
    have hh:=S.sum_degrees_eq_twice_card_edges
    have hdeg:∀v,S.degree v=2*m:=hregular
    simp only [hdeg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh ⊢
    nlinarith [hh]
  obtain ⟨M,hphys,hout,havoid,hchange⟩:=orientationRouting S E Protected M₀ (fun _=>m) L hL hn
    ha hf hβ hphysical htotal herr hforbid hpaths hmargin
  refine ⟨M,hphys,?_,havoid,hchange⟩
  intro v
  have hd:=orientationMatrix_degree S M hphys v
  rw [hout v,hregular v] at hd
  exact ⟨hout v,by omega⟩
end Oberwolfach
