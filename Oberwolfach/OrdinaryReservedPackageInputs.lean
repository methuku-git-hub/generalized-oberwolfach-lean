module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage
public import Oberwolfach.OrdinaryUnreservedResidualOldInputs
public import Oberwolfach.RawReservedSpokeList

@[expose] public section
/-! A coherent matched package supplies the source, old-image and selected
reserved-spoke avoidance hypotheses needed for forced placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_package_inputs
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {A B J W:U→Type} [∀u,Fintype (A u)] [∀u,DecidableEq (A u)]
    [∀u,Fintype (B u)] [∀u,DecidableEq (B u)] [∀u,Fintype (J u)] [∀u,DecidableEq (J u)]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (m d:ℕ) (π:Equiv.Perm (Fin n))
    (σI:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (root:∀u,A u⊕B u→Fin n) (Arc:Fin n→Fin n→Prop) (Avail:U→Finset (Fin n))
    (Good:∀u,W u→Prop) (Pack:∀u,W u→Finset (Finset (Fin n)))
    (Pos:∀u,W u→B u→Finset ℕ) (len:∀u,J u→ℕ):
    let S:=fun u:U=>{x:Fin n | (F u).connectedComponentMk x∉Cres u}
    let X:=fun u=>↥(S u)
    let H:=fun u=>(F u).induce (S u);
    ∀p:∀u,OrdinaryMatchedResidualHubPackage (H u) m d π (root u) Arc (Avail u)
      (rawReservedSpokeList π d σI u) (Good u) (Pack u) (Pos u) (len u),
    let data:=fun u=>(p u).data
    let Old:=fun u=>(data u).oldDomain\bufferedPathStrictInterior (fun _:A u=>(m+1)*d) (p u).inner
    let ψ:=fun u=>(p u).ψ;
    (∀u,(H u).IsRegularOfDegree 2) ∧
    (∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed) ∧
    (∀u,(data u).prescribed⊆Old u) ∧
    (∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u))) ∧
    (∀u,Disjoint (rawReservedSpokeList π d σI u) ((Old u).image (ψ u))) ∧
    (∀u,ActualOldImageDirected (data u) (ψ u) Arc) ∧
    (∀u,ActualOldPhysicalCoverage (data u) (ψ u) (Pack u (p u).marker)) :=by
  intro S X H p data Old ψ
  obtain ⟨hreg,hCycle,hPres⟩:=ordinary_unreserved_residual_restricted_old_inputs F hF Cres (m+1) d
    data (fun u=>(p u).ext) (fun u=>(p u).inner)
    (fun u=>(p u).hc) (fun u=>(p u).hd) (fun u=>(p u).hs₁)
    (fun u=>(p u).hSupp) (fun u=>(p u).hInner) (fun u=>(p u).hEmbed)
  exact ⟨hreg,hCycle,hPres,fun u=>(p u).hInjective,fun u=>(p u).hAvoidReserve.symm,
    fun u=>(p u).hDirected,fun u=>(p u).hCoverage⟩
end Oberwolfach
