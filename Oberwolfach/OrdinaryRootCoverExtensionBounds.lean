module

public import Oberwolfach.OrdinaryRootCoverData
public import Oberwolfach.OrdinaryInnerExtensionsAfterLocalCover

@[expose] public section
/-! Pass parent extension lower bounds through the actual root cover, losing
only three times its inner physical degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_extension_bounds (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell b:ℝ)
    (A:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (hcount:∀u∈Z,∀a∈X,∀c∈X,b≤
      (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)):
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    ∀u∈Z,∀a∈X,∀c∈X,b-3*η≤
      (((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ):=by
  intro Q' H' u hu a ha c hc
  have horig:=hcount u hu a ha c hc
  have hsurvive:=ordinary_inner_extensions_after_local_cover Q A.rim H A.spokes X Z η A.inner_degree u hu a c ha hc
  linarith only [horig,hsurvive]
end Oberwolfach
