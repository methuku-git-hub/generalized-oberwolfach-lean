module

public import Oberwolfach.OrdinaryVortexInitialLocalExactBalance
public import Oberwolfach.OrdinaryFixedVortexConflictDegree

@[expose] public section
/-! At the initial level, global conflict avoidance, balance and divisibility
restrict to the local certificate domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_wheel_structural_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d r:ℕ)
    (hdis:Disjoint G (permutationConflictGraph π (3*d)))
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card):
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let Gloc:=G.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Hloc:=fun v u=>Hs (f v) (g u);
    Disjoint Gloc Floc ∧ (∀v,Floc.degree v≤2*(3*d)) ∧
    (∀v,(Floc.degree v:ℝ)≤2*((3*d:ℕ):ℝ)) ∧
    (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hloc v u)).card) :=by
  intro f g Gloc Floc Hloc
  have hlocalDis:Disjoint Gloc Floc:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (disjoint_iff_inf_le.mp hdis) ⟨hvw.1,hvw.2⟩
  have hF:∀v,Floc.degree v≤2*(3*d):=by
    intro v
    exact ordinary_fixed_vortex_conflict_degree P D mv β ε Q π hπ 0 (3*d) v
  have hFr:∀v,(Floc.degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    exact_mod_cast hF v
  have hexact:=ordinary_vortex_initial_local_exact_balance P G Hs D mv β ε Q r hbal hdiv
  exact ⟨hlocalDis,hF,hFr,hexact.1,hexact.2⟩
end Oberwolfach
