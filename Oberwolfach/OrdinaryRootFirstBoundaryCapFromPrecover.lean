module

public import Oberwolfach.OrdinaryRootFirstPrecoverSelectionData
public import Oberwolfach.BoundaryDegreeAfterPacking
public import Oberwolfach.OrdinaryBoundaryRowSumFromBoundary

@[expose] public section
/-! The pre-cover reserve bounds both the cleaned boundary degree and
the total size of its outside-root spoke classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_boundary_cap_from_precover
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ)
    (p ε:ℝ) (ht:0≤t) (hp:0≤p)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p ε σ) (Dmax:ℕ)
    (hcap:(p+ε)*Fintype.card (V⊕U)+(t+ν)≤Dmax):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O;
    (∀w:V⊕U,(ordinaryBoundaryGraph Q₂ H₂ X Z).degree w≤Dmax) ∧
    Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)≤Fintype.card (V⊕U)*Dmax:=by
  intro Q₂ H₂
  let C:=ordinaryRootFirstPrecoverPrior Q F H X T Z W r η ell t O.context σ
  let J:=ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels)
  have hf:=ordinary_root_first_precover_selection_data Q Qfactor F H Hfactor X T Z W r η ell t ν D σ O ht hbase
  have hb:=boundary_degree_after_packing (ordinaryBoundaryGraph Q H X Z) C J σ p ε (t+ν)
    hp hsample hf.1 hf.2.2.2.1
  have hd:∀w:V⊕U,(ordinaryBoundaryGraph Q₂ H₂ X Z).degree w≤Dmax:=by
    intro w
    have hh:((ordinaryBoundaryGraph Q₂ H₂ X Z).degree w:ℝ)≤
        ((((ordinaryBoundaryGraph Q H X Z\C)\J).degree w):ℝ):=by
      exact_mod_cast SimpleGraph.degree_le_of_le hf.2.2.1 (v:=w)
    have hbound:=hh.trans ((hb w).trans hcap)
    exact_mod_cast hbound
  exact ⟨hd,ordinary_boundary_row_sum_bound_from_boundary Q₂ H₂ X Z Dmax hd⟩
end Oberwolfach
