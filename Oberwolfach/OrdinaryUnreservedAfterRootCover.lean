module

public import Oberwolfach.OrdinaryRootCoverData
public import Oberwolfach.OrdinaryUnreservedPackingCertificate

@[expose] public section
/-! After the deeper roots have been covered, every unreserved resource
avoids those roots. Removing them from the active domains therefore loses no
unreserved rim edge or spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_after_root_cover
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (A:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (R:SimpleGraph (V⊕U)):
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    (∀v∈T,∀w,¬(ordinaryUnreservedRim Q' X R).Adj v w) ∧
    (∀v∈T,∀u,¬ordinaryUnreservedSpokes H' X Z R v u) ∧
    (∀u∈W,∀v,¬ordinaryUnreservedSpokes H' X Z R v u):=by
  intro Q' H'
  refine ⟨?_,?_,?_⟩
  · intro v hv w hw
    by_cases hwX:w∈X
    · apply hw.1.2
      exact (spanningRestriction_adj Q' X v w).mpr ⟨hw.1.1,hTX hv,hwX⟩
    · exact hw.1.1.2 (A.covers_rim v hv w hwX hw.1.1.1)
  · intro v hv u hu
    by_cases huZ:u∈Z
    · exact hu.2.1 ⟨hTX hv,huZ⟩
    · exact hu.1.2 (A.covers_row v hv u huZ hu.1.1)
  · intro u hu v hv
    by_cases hvX:v∈X
    · exact hv.2.1 ⟨hvX,hWZ hu⟩
    · exact hv.1.2 (A.covers_column u hu v hvX hv.1.1)
end Oberwolfach
