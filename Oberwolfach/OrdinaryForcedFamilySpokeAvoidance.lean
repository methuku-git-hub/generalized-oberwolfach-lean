module

public import Oberwolfach.OrdinaryForcedInnerReferenceAvoidance

@[expose] public section
/-! Apply the reserved-spoke avoidance to every actual complementary factor
    using the same forced-target placement and sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_forced_family_avoids_reference_spokes
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    {X A K J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (K u)] [∀u,DecidableEq (J u)]
    (F:∀u,SimpleGraph (X u)) (data:∀u,ActualResidualData (K:=K u) (J:=J u) (F u))
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (len:∀u,A u→ℕ) (inner:∀u (i:A u),Fin (len u i+1)↪X u) (hempty:∀u,IsEmpty (A u))
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (ψ:∀u,X u→V) (f:∀u,X u↪V)
    (Φ g:∀u,{x:X u // x∈(data u).remaining}→V) (B:∀u,Finset {x:X u // x∈(data u).remaining})
    (Ends:U→Finset V) (Old:∀u,Finset (X u)) (Inner:Finset V) (Hubs:Finset U)
    (hOld:∀u x,x∈(data u).oldDomain→f u x=ψ u x)
    (hRem:∀u (x:{x:X u // x∈(data u).remaining}),f u x.val=Φ u x)
    (hOn:∀u x,x∈B u→Φ u x=g u x)
    (hOutside:∀u x,x∉B u→Φ u x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hImage:∀u,let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
      let T:=ordinaryInnerSpokeTargets Inner Hubs Href u;
      (B u).image (g u)=(residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.val)∪Ends u∪((T\(Old u).image (ψ u))\Ends u))
    (hEnds:∀u,Ends u⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hOldBad:∀u,Disjoint (((data u).oldDomain\bufferedPathStrictInterior (len u) (inner u)).image (ψ u))
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u)):
    ∀u x,¬rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false (f u x) u:=by
  intro u
  exact ordinary_forced_inner_embedding_avoids_reference_spokes (F u) (data u) (hCycle u) (len u) (inner u) (hempty u)
    π d hd σ t Jret u (ψ u) (f u) (Φ u) (g u) (B u) (Ends u) (Old u) Inner Hubs
    (hOld u) (hRem u) (hOn u) (hOutside u) (hImage u) (hEnds u) (hOldBad u)
end Oberwolfach
