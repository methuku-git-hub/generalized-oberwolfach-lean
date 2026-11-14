module

public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance
public import Oberwolfach.OrdinaryVortexBufferedDomains

@[expose] public section
/-! A protected later history supplies the same local host, nested roots,
and exact balance conditions required by the triangle certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_later_local_basics
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P G F Qstart:SimpleGraph V) (H Hstart:V→U→Prop) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (i:ℕ) (cost deepCost:ℕ→ℝ) (A:Finset (Sym2 V⊕(V×U)))
    (hhost:G≤P\F)
    (htrace:OrdinaryProtectedTrace Qstart Hstart (fun k=>Q.extendedVertices (k+1)) (fun k=>Q.extendedVertices (k+2))
      (fun k=>Q.extendedIndices (k+1)) (fun k=>Q.extendedIndices (k+2)) cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G H=A)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card):
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let Gloc:=G.comap f;let Ploc:=P.comap f;let Floc:=F.comap f;
    let Hloc:=fun v u=>H (f v) (g u);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let T:=ordinaryVortexBufferedVertices Q (i+1) 2;let W:=ordinaryVortexBufferedHubs Q (i+1) 2;
    Gloc≤Ploc\Floc ∧ Disjoint Gloc Floc ∧ T⊆I ∧ W⊆B ∧
    (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀u,3∣(Finset.univ.filter (fun v=>Hloc v u)).card) :=by
  intro f g Gloc Ploc Floc Hloc I B T W
  have hloc:Gloc≤Ploc\Floc:=by intro v w hvw;exact hhost hvw
  have hdis:Disjoint Gloc Floc:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hloc hvw.1).2 hvw.2
  have hnested:=ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)
  have hexact:=ordinary_vortex_trace_local_exact_balance P Qstart G Hstart H D mv β ε Q 3 i cost deepCost A htrace hstate hbal hdiv
  exact ⟨hloc,hdis,hnested.2.2.1,hnested.2.2.2,hexact.1,hexact.2⟩
end Oberwolfach
