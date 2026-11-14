module

public import Oberwolfach.OrdinaryZeroRetainedPackageOldHost

@[expose] public section
/-! The host and reference-avoidance conclusions hold simultaneously for
the old edges of the selected coherent family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_zero_retained_family_old_host
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B J W:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,Fintype (B u)] [∀u,DecidableEq (B u)]
    [∀u,Fintype (J u)] [∀u,DecidableEq (J u)]
    (F:∀u,SimpleGraph (X u)) (m d:ℕ) (π:Equiv.Perm (Fin n))
    (root:∀u,A u⊕B u→Fin n) (P Host Del Bad:SimpleGraph (Fin n)) (hHost:Host≤P)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Avail Reserve:U→Finset (Fin n)) (Good:∀u,W u→Prop) (Pack:∀u,W u→Finset (Finset (Fin n)))
    (Pos:∀u,W u→B u→Finset ℕ) (length:∀u,J u→ℕ)
    (pkg:∀u,OrdinaryMatchedResidualHubPackage (F u) m d π (root u)
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))
      (Avail u) (Reserve u) (Good u) (Pack u) (Pos u) (length u))
    (hempty:∀u,IsEmpty (A u)):
    let Old:=fun u=>(pkg u).data.deletedEdges.image (Sym2.map (pkg u).ψ);
    (∀u,Old u⊆P.edgeFinset) ∧
    (∀u,Disjoint (Old u) (longPhysicalStateGraph P σ {0}\Bad).edgeFinset) :=by
  intro Old
  constructor
  · intro u
    exact (ordinary_zero_retained_package_old_host (F u) m d π (root u) P Host Del Bad hHost σ
      (Avail u) (Reserve u) (Good u) (Pack u) (Pos u) (length u) (hempty u) (pkg u)).1
  · intro u
    exact (ordinary_zero_retained_package_old_host (F u) m d π (root u) P Host Del Bad hHost σ
      (Avail u) (Reserve u) (Good u) (Pack u) (Pos u) (length u) (hempty u) (pkg u)).2
end Oberwolfach
