module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage
public import Oberwolfach.OrdinaryOldApproximateAvoidsReference
public import Oberwolfach.OrdinarySampledSurvivalTarget

@[expose] public section
/-! For zero retained final paths, the package's actual old edge images
are in the original host and avoid the reference, on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_zero_retained_package_old_host
    {n:ℕ} {U X A B J W:Type} [Fintype U] [DecidableEq U]
    [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
    (F:SimpleGraph X) (m d:ℕ) (π:Equiv.Perm (Fin n)) (root:A⊕B→Fin n)
    (P Host Del Bad:SimpleGraph (Fin n)) (hHost:Host≤P)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Avail Reserve:Finset (Fin n)) (Good:W→Prop) (Pack:W→Finset (Finset (Fin n)))
    (Pos:W→B→Finset ℕ) (length:J→ℕ) (hempty:IsEmpty A)
    (pkg:OrdinaryMatchedResidualHubPackage F m d π root
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))
      Avail Reserve Good Pack Pos length):
    let Old:=pkg.data.deletedEdges.image (Sym2.map pkg.ψ);
    Old⊆P.edgeFinset ∧ Disjoint Old (longPhysicalStateGraph P σ {0}\Bad).edgeFinset :=by
  intro Old
  have hdel:longPhysicalStateGraph P σ {0,1,2,3,4}\P≤Del:=by
    intro x y h
    exact (h.2 h.1.1).elim
  have hArc:∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→P.Adj x y:=
    (ordinary_sampled_survival_in_target P P Host Del hHost π d σ hdel).2
  have hhost:=actual_old_directed_physical_host pkg.data pkg.ψ P _ hArc pkg.hDirected
  have hfinal:=actual_final_edges_empty_of_empty_first_index pkg.data hempty pkg.hs₁
  rw [hfinal,Finset.sdiff_empty] at hhost
  have href:=ordinary_old_approximate_edges_disjoint_reference pkg.data pkg.ψ hempty pkg.hs₁ Host P Del π d σ pkg.hDirected
  refine ⟨hhost,?_⟩
  apply Finset.disjoint_left.mpr
  intro e he hrefbad
  apply Finset.disjoint_left.mp href he
  induction e using Sym2.ind with
  | _ x y =>
    exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeFinset.mp hrefbad).1
end Oberwolfach
