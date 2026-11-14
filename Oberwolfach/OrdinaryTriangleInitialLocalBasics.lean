module

public import Oberwolfach.OrdinaryVortexInitialLocalExactBalance
public import Oberwolfach.OrdinaryVortexBufferedDomains

@[expose] public section
/-! The balanced initial tracked remainder is a valid local triangle host,
and its buffered deeper domains are nested in the same parent pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_initial_local_basics
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P G F:SimpleGraph V) (H:V→U→Prop) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (hhost:G≤P\F)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card):
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let Gloc:=G.comap f;let Ploc:=P.comap f;let Floc:=F.comap f;
    let Hloc:=fun v u=>H (f v) (g u);
    let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let T:=ordinaryVortexBufferedVertices Q 0 2;let W:=ordinaryVortexBufferedHubs Q 0 2;
    Gloc≤Ploc\Floc ∧ Disjoint Gloc Floc ∧ T⊆I ∧ W⊆B ∧
    (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀u,3∣(Finset.univ.filter (fun v=>Hloc v u)).card) :=by
  intro f g Gloc Ploc Floc Hloc I B T W
  have hloc:Gloc≤Ploc\Floc:=by
    intro v w hvw
    exact hhost hvw
  have hdis:Disjoint Gloc Floc:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hloc hvw.1).2 hvw.2
  have hnested:=ordinary_vortex_buffered_nested Q 0 2 (by omega)
  have hexact:=ordinary_vortex_initial_local_exact_balance P G H D mv β ε Q 3 hbal hdiv
  exact ⟨hloc,hdis,hnested.2.2.1,hnested.2.2.2,hexact.1,hexact.2⟩
end Oberwolfach
