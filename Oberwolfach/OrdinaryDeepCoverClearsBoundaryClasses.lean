module

public import Oberwolfach.OrdinaryRootClearedBoundaryClasses
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! A packing that covers every unreserved resource at the deeper roots
clears those roots from all outer boundary classes. The reserved resources
are allowed only inside the enclosing pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_cover_clears_boundary_classes
    (Q Rreserved Rused:SimpleGraph V) (H Sreserved Sused:V→U→Prop)
    (X T:Finset V) (Z W:Finset U)
    (hRreserved:Rreserved≤spanningRestriction Q X)
    (hSreserved:∀v u,Sreserved v u→v∈X∧u∈Z)
    (hRcover:∀v∈T,∀w,(Q\Rreserved).Adj v w→Rused.Adj v w)
    (hSrow:∀v∈T,∀u,H v u∧¬Sreserved v u→Sused v u)
    (hScol:∀u∈W,∀v,H v u∧¬Sreserved v u→Sused v u):
    let Q':=Q\Rused;let H':=fun v u=>H v u∧¬Sused v u;
    (∀i,ordinaryBoundaryRimSet Q' X i⊆X\T) ∧
    (∀i,ordinaryBoundaryRowSet H' X Z i⊆Z\W) ∧
    (∀j,ordinaryBoundaryHubSet H' Z X j⊆X\T):=by
  intro Q' H'
  apply ordinary_root_cleared_boundary_classes Q' H' X T Z W
  · intro v hv w hw hadj
    have hnot:¬Rreserved.Adj v w:=by
      intro hh
      exact hw ((spanningRestriction_adj Q X v w).mp (hRreserved hh)).2.2
    exact hadj.2 (hRcover v hv w ⟨hadj.1,hnot⟩)
  · intro v hv u hu hadj
    have hnot:¬Sreserved v u:=by
      intro hh;exact hu (hSreserved v u hh).2
    exact hadj.2 (hSrow v hv u ⟨hadj.1,hnot⟩)
  · intro u hu v hv hadj
    have hnot:¬Sreserved v u:=by
      intro hh;exact hv (hSreserved v u hh).1
    exact hadj.2 (hScol u hu v ⟨hadj.1,hnot⟩)
end Oberwolfach
