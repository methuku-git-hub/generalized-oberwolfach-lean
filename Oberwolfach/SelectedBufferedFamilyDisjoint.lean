module

public import Oberwolfach.SelectedBufferedPathRestriction

@[expose] public section
/-! Physical edge disjointness survives passage to selected final intervals. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_buffered_path_family_disjoint
    {U X Y:Type*} [DecidableEq X]
    (I:U→Type*) [∀u,Fintype (I u)] [∀u,DecidableEq (I u)]
    (G:U→SimpleGraph X) (S:∀u,Finset (I u)) (n:∀u,I u→ℕ)
    (inner:∀u (i:I u),Fin (n u i+1)↪X)
    (f:∀u,{x // x∈bufferedPathFullDomain (n u) (inner u)}↪Y)
    (hdis:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set X)) (f u))
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n v) (inner v)}
        ((G v).induce (↑(bufferedPathFullDomain (n v) (inner v)):Set X)) (f v))) :
    ∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly
        {x // x∈bufferedPathFullDomain (bufferedSelectedLengths (S u) (n u)) (bufferedSelectedPaths (S u) (n u) (inner u))}
        ((G u).induce (↑(bufferedPathFullDomain (bufferedSelectedLengths (S u) (n u)) (bufferedSelectedPaths (S u) (n u) (inner u))):Set X))
        (restrictBufferedPathMap (S u) (n u) (inner u) (f u)))
      (partialFactorPhysicalEdgesPoly
        {x // x∈bufferedPathFullDomain (bufferedSelectedLengths (S v) (n v)) (bufferedSelectedPaths (S v) (n v) (inner v))}
        ((G v).induce (↑(bufferedPathFullDomain (bufferedSelectedLengths (S v) (n v)) (bufferedSelectedPaths (S v) (n v) (inner v))):Set X))
        (restrictBufferedPathMap (S v) (n v) (inner v) (f v))) := by
  intro u v huv
  exact (hdis u v huv).mono
    (partial_factor_physical_edges_restrict (G u) (buffered_selected_domain_subset (S u) (n u) (inner u)) (f u))
    (partial_factor_physical_edges_restrict (G v) (buffered_selected_domain_subset (S v) (n v) (inner v)) (f v))
end Oberwolfach
