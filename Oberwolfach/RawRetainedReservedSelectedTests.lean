module

public import Oberwolfach.RawReservedSelectedNeighbourTests
public import Oberwolfach.MarkedExpandedRetainedProjection
public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! Reserved-label neighbourhood tests descend to the retained reference
law.  This permits them to share an extra-event budget with the parent and
occupancy events before the expanded matching outcome is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawReferenceNeighbourTestSet {V:Type} [Fintype V] [LinearOrder V]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Option (Bool×Bool)):
    RawNeighbourTestIndex V→Finset V
  | none=>Finset.univ
  | some (.inl x)=>directedOutNeighbours (fun x y=>markedPhysicalRim P π (3*d) ω false x y=1) x
  | some (.inr (.inl y))=>directedInNeighbours (fun x y=>markedPhysicalRim P π (3*d) ω false x y=1) y
  | some (.inr (.inr (x,y)))=>directedOutNeighbours (fun x y=>markedPhysicalRim P π (3*d) ω false x y=1) x ∩
      directedInNeighbours (fun x y=>markedPhysicalRim P π (3*d) ω false x y=1) y

theorem raw_retained_reserved_selected_tests_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V] [Nonempty V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    Fintype.card U≤Fintype.card V→
    ∀(color:Color) (g:Γ) (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ)
    (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀w a,0≤q w a) (hQ:∀w,∑a,q w a≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑a,q w a))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    1-δ≤(rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) w color
          (rawReferenceNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawReferenceNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s w color|<
          (Fintype.card V:ℝ)^(3/4:ℝ)) := by
  obtain ⟨N,hN⟩:=raw_reserved_selected_neighbour_tests_high_probability d hd δ hδ
  refine ⟨N,?_⟩
  intro V _ _ _ hn U Γ Color _ _ _ _ hU color g P π p k hp hk hphys q hq hQ s hs hS hnoshort
  let F:=fun a:RawMarkedOutcome V U Γ Color=>StartRetentionOutcome
    (rawStartHubSet π d (fun e=>a (Sum.inr e)) g)
    (startRetentionMinimum (rawStartHubSet π d (fun e=>a (Sum.inr e)) g))
  let ν:=fun a:RawMarkedOutcome V U Γ Color=>startRetentionLaw
    (rawStartHubSet π d (fun e=>a (Sum.inr e)) g)
    (startRetentionMinimum (rawStartHubSet π d (fun e=>a (Sum.inr e)) g)) (startRetentionMinimum_le _)
  let E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g→Prop:=fun z=>
    ∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) w color
      (rawReferenceNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
      (rawReferenceNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s w color|<
      (Fintype.card V:ℝ)^(3/4:ℝ)
  have hsum:2*p+2*k+2*(0:ℝ)+2*(0:ℝ)+0≤1:=by linarith
  have hTest:=hN V hn U Γ Color hU color P π p k 0 0 0 hp hk (by norm_num) (by norm_num) (by norm_num)
    hsum q hq hQ s hs hS hnoshort F ν
  have hproj:=raw_expanded_marked_retained_projection_probability p k 0 0 0 hp hk (by norm_num) (by norm_num)
    (by norm_num) hsum d hd q hq hQ s hs hS F ν E
  have hevent:∀(z:Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (fun e=>rawExpandedMarkedCollapse e (ω e))),
    (∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) w color
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s w color|<
          (Fintype.card V:ℝ)^(3/4:ℝ)) ↔
      E ⟨(fun e=>rawExpandedMarkedCollapse e (z.1 e)),z.2⟩:=by
    intro z
    rfl
  change 1-δ≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hphys d hd q hq hQ s hs hS)).sigma ν).probability E
  rw [←hproj]
  simp_rw [←hevent]
  exact hTest
end Oberwolfach
