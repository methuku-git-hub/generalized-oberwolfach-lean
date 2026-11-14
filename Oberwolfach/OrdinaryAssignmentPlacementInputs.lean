module

public import Oberwolfach.OrdinaryPairAssignmentCommonEvent
public import Oberwolfach.PrescribedBadEdgeAssignments
public import Oberwolfach.PrescribedMatchingOccurrenceBound

@[expose] public section
/-! Convert the protected assignment on the realized sample into the exact
matching, physical-disjointness and endpoint-load inputs for simultaneous
residual placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assignment_gives_placement_matching_inputs
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (a:ℝ) (hEvent:OrdinaryProtectedBadEdgeAssignments π d σ a)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (G:SimpleGraph (Fin n)) (Dstar:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (Old:U→Finset (Fin n))
    (hOld:∀u,Disjoint (Old u) (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u))
    (b:ℝ) (hb:0≤b) (hbsmall:b≤a/16) (hdegree:∀v,(G.degree v:ℝ)≤b*n):
    ∃M:U→Finset (Fin n×Fin n),
      (∀u,IsPrescribedOrientedMatching (M u)) ∧
      (∀u,Disjoint (Old u) (prescribedMatchingEndpoints (M u))) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) ∧
      (∀u,(M u).card≤⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊) ∧
      (∀u x y,(x,y)∈M u→Dstar x y) ∧
      (∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset) ∧
      PairwisePhysicalDisjoint (fun u=>(M u).image prescribedArcPhysical) ∧
      (∀e∈G.edgeFinset,∃u,e∈(M u).image prescribedArcPhysical) ∧
      (∀v,(Finset.univ.filter (fun u=>v∈prescribedMatchingEndpoints (M u))).card≤G.degree v):=by
  obtain ⟨assign,orient,horient,hallowed,hold,hmatching,hcard⟩:=
    hEvent t Jret G Dstar hDstar Old (fun u=>(hOld u).symm) b hb hbsmall hdegree
  let M:=prescribedAssignedArcs G assign orient
  have hphys:=prescribed_assigned_arcs_physical G assign orient (fun e he=>(horient e he).1)
  refine ⟨M,hmatching,hold,?_,hcard,?_,?_,hphys.2.2,?_,?_⟩
  · intro u v hv
    obtain ⟨arc,harc,hv⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp harc
    have heG:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
    have heU:assign e=u:=(Finset.mem_filter.mp he).2
    have hve:v∈e.toFinset:=by
      rw [←(horient e heG).1]
      simp only [prescribedArcPhysical,Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton]
      simpa [heq] using hv
    have hl:=hallowed e heG
    rw [heU] at hl
    have hl' : ∀v∈e.toFinset,v∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u := by
      simpa [protectedPairEdgeHubs] using hl
    exact hl' v hve
  · intro u x y hxy
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp hxy
    have hmem:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
    have hh:=(horient e hmem).2
    simpa only [heq] using hh
  · intro u e he
    exact (hphys.1 u e he).1
  · intro e he
    exact ⟨assign e,hphys.2.1 e he⟩
  · intro v
    exact prescribed_matching_endpoint_occurrences M G (fun u e he=>(hphys.1 u e he).1) hphys.2.2 v
end Oberwolfach
