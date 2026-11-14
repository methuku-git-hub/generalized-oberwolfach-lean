module

public import Oberwolfach.ClassOrientationRouting
public import Oberwolfach.ClassOrientationCorrectionGraph

@[expose] public section
/-! Balance the actual regular class, keep protected directions fixed, and
bound the deletion relative to the original sampled class graph. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_balanced_correction
    {V:Type} [Fintype V] [LinearOrder V]
    (S₀ S Protected:SimpleGraph V) (bits:Sym2 V→Bool) (m L:ℕ)
    (hregular:S.IsRegularOfDegree (2*m)) (hL:0<L) (hn:0<Fintype.card V)
    (a f β b:ℝ) (ha:0≤a) (hf:0≤f) (hβ:0<β)
    (hprotected:∀x y,Protected.Adj x y→(S.Adj x y↔S₀.Adj x y))
    (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤b)
    (herr:∀v,|((∑w,sampledOrientation S bits v w:ℕ):ℝ)-m|≤a)
    (hforbid:∀v,(Protected.degree v:ℝ)≤f)
    (hpaths:∀x y,x≠y→β*Fintype.card V≤
      ((Finset.univ.filter (fun z=>0<sampledOrientation S bits x z ∧ 0<sampledOrientation S bits z y ∧
        S.Adj x z ∧ S.Adj z y)).card:ℝ))
    (hmargin:(Fintype.card V:ℝ)*a/L+2*a+4*L+2*f<β*Fintype.card V):
    ∃M:V→V→ℕ,
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m) ∧
      (∀v,((orientationDisagreementGraph S₀ bits M).degree v:ℝ)≤b+a+2*L) ∧
      (∀x y,(orientationDisagreementGraph S₀ bits M).Adj x y→¬Protected.Adj x y):=by
  obtain ⟨M,hphys,hbalanced,havoid,hchange⟩:=class_orientation_routing S S Protected
    (sampledOrientation S bits) m L hregular hL hn a f β ha hf hβ
    (sampledOrientation_physical S bits) herr hforbid hpaths hmargin
  refine ⟨M,hphys,hbalanced,?_,?_⟩
  · intro v
    have hh:=class_orientation_correction_degree S₀ S bits M v
    linarith [hedit v,hchange v]
  · intro x y hDel hP
    have hS:S.Adj x y:=(hprotected x y hP).2 hDel.1
    have heq1:sampledOrientation S bits x y=sampledOrientation S₀ bits x y:=by
      simp [sampledOrientation,hS,hDel.1]
    have heq2:sampledOrientation S bits y x=sampledOrientation S₀ bits y x:=by
      simp [sampledOrientation,hS.symm,hDel.1.symm]
    have hchanged:M x y≠sampledOrientation S bits x y ∨ M y x≠sampledOrientation S bits y x:=by
      simpa only [heq1,heq2] using hDel.2
    exact (havoid x y hchanged).2 hP
end Oberwolfach
