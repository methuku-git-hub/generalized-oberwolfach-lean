module

public import Oberwolfach.OrdinaryRootCoverData

@[expose] public section
/-! Removing a root-cover wheel decomposition preserves balance and clears
the root boundary classes on the actual host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_remainder_facts (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (A:OrdinaryRootCoverData Q F H X T Z W r η ell):
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    (∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) ∧
    (∀v∈T,∀w∉X,¬Q'.Adj v w) ∧
    (∀v∈T,∀u∉Z,¬H' v u) ∧
    (∀u∈W,∀v∉X,¬H' v u):=by
  intro Q' H'
  have hb:=ordinary_decomposition_remainder_balance Q A.rim H A.spokes r A.rim_sub A.spoke_sub hbal hdiv A.decomposition
  refine ⟨hb.1,hb.2,?_,?_,?_⟩
  · intro v hv w hw hh;exact hh.2 (A.covers_rim v hv w hw hh.1)
  · intro v hv u hu hh;exact hh.2 (A.covers_row v hv u hu hh.1)
  · intro u hu v hv hh;exact hh.2 (A.covers_column u hu v hv hh.1)
end Oberwolfach
