module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage
public import Oberwolfach.OrdinaryForcedFamilySpokeAvoidance

@[expose] public section
/-! The reserved-spoke avoidance carried by coherent matching packages
supplies the reference-spoke condition for the forced complement embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_packaged_forced_spoke_avoidance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B J W:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,Fintype (B u)] [∀u,DecidableEq (B u)]
    [∀u,Fintype (J u)] [∀u,DecidableEq (J u)]
    (F:∀u,SimpleGraph (X u)) (m d:ℕ) (hd:1≤d) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (root:∀u,A u⊕B u→Fin n) (Arc:Fin n→Fin n→Prop)
    (Good:∀u,W u→Prop) (Pack:∀u,W u→Finset (Finset (Fin n)))
    (Pos:∀u,W u→B u→Finset ℕ) (len:∀u,J u→ℕ)
    (p:∀u,OrdinaryMatchedResidualHubPackage (F u) m d π (root u) Arc
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u)
      (Good u) (Pack u) (Pos u) (len u))
    (hempty:∀u,IsEmpty (A u))
    (f:∀u,X u↪Fin n)
    (Φ g:∀u,{x:X u // x∈(p u).data.remaining}→Fin n)
    (Bset:∀u,Finset {x:X u // x∈(p u).data.remaining})
    (Ends:U→Finset (Fin n)) (Inner:Finset (Fin n)) (Hubs:Finset U):
    let data:=fun u=>(p u).data
    let ψ:=fun u=>(p u).ψ
    let Old:=fun u=>(data u).oldDomain\bufferedPathStrictInterior (fun _:A u=>(m+1)*d) (p u).inner;
    (∀u x,x∈(data u).oldDomain→f u x=ψ u x)→
    (∀u (x:{x:X u // x∈(data u).remaining}),f u x.val=Φ u x)→
    (∀u x,x∈Bset u→Φ u x=g u x)→
    (∀u x,x∉Bset u→Φ u x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)→
    (∀u,let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
      let T:=ordinaryInnerSpokeTargets Inner Hubs Href u;
      (Bset u).image (g u)=(residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.val)∪Ends u∪((T\(Old u).image (ψ u))\Ends u))→
    (∀u,Ends u⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)→
    ∀u x,¬rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false (f u x) u :=by
  intro data ψ Old hOld hRem hOn hOutside hImage hEnds
  have hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed:=by
    intro u
    rw [(p u).hEmbed]
  have hBad:∀u,Disjoint (((data u).oldDomain\bufferedPathStrictInterior (fun _:A u=>(m+1)*d) (p u).inner).image (ψ u))
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u):=fun u=>(p u).hAvoidReserve
  exact ordinary_forced_family_avoids_reference_spokes F data hCycle (fun _ _=>(m+1)*d) (fun u=>(p u).inner) hempty
    π d hd σ t Jret ψ f Φ g Bset Ends Old Inner Hubs hOld hRem hOn hOutside hImage hEnds hBad
end Oberwolfach
