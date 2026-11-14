module

public import Oberwolfach.MarkedVortexActiveDomainEquivalences
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! The first active domain retains at least three quarters of the first
vortex vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_first_active_relative_size
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0≤ε) (hε1:ε≤1/4):
    (3/4:ℝ)*(Q.extendedVertices 1).card≤
      Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)) :=by
  have hv:=nested_contracting_difference_sizes Q.extendedVertices ε hε hε1
    (fun i j h=>Q.extendedVertices_subset h) (fun i=>(Q.extended_successor_size_bounds hε i).1) 1 1 (by omega)
  have hequiv:Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))=
      (Q.extendedVertices 1\Q.extendedVertices 2).card:=by
    have hh:=Fintype.card_congr (markedVortexActiveVertexEquiv Q 1)
    change Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))=
      Fintype.card ↥(Q.extendedVertices 1\Q.extendedVertices (1+1)) at hh
    simpa only [Fintype.card_coe,show 1+1=2 by omega] using hh
  simpa only [hequiv,show 1+1=2 by omega] using hv.1
end Oberwolfach
