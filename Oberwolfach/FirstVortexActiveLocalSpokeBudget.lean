module

public import Oberwolfach.FirstActiveLocalSpokeBudget
public import Oberwolfach.MarkedVortexFirstActiveRelativeSize
public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
/-! Apply the local-spoke arithmetic to the actual first vortex and its
first active vertex domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_active_local_spoke_budget
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0<ε) (hε1:ε≤1/4) (hm:0<m)
    (cap θ ζ P L err defect:ℝ) (hcap:0≤cap)
    (hθ:θ≤cap/128) (hζ:ζ≤cap/128)
    (hP:P≤cap*(ε*Fintype.card V)/128) (hL:2*L≤cap*(ε*Fintype.card V)/128)
    (herr:err≤cap*(ε*Fintype.card V)/128) (hdefect:defect≤cap*(ε*Fintype.card V)/128):
    let I:ℝ:=(Q.extendedVertices 1).card
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1));
    (ζ*I+P+2*L)+(2*θ*I+err+2*ζ*I+defect)≤cap*Fintype.card W :=by
  intro I W
  have hI:0≤I:=by dsimp [I]; positivity
  have hN:ε*(Fintype.card V:ℝ)≤2*I:=by
    have hh:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
    dsimp only [I]
    linarith
  have hW:3*I/4≤(Fintype.card W:ℝ):=by
    have hh:=marked_vortex_first_active_relative_size G D m β ε Q hε.le hε1
    dsimp only [I,W]
    nlinarith only [hh]
  exact first_active_local_spoke_budget cap θ ζ (ε*Fintype.card V) I (Fintype.card W) P L err defect
    hcap hI hN hW hθ hζ hP hL herr hdefect
end Oberwolfach
