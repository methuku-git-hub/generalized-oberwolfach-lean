module

public import Oberwolfach.RawUnassignedAdaptiveHighProbability
public import Oberwolfach.RawUnassignedExtendingList
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! The at-most-quadratic family of in-, out-, and mixed neighbourhood tests
is allowed to depend on the independent sampled physical-edge coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawApproxPhysicalRelation {V:Type} [Fintype V] [LinearOrder V]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (x y:V):Prop:=
  markedPhysicalRim P π (3*d) (fun e=>markedExpandedApproximateCollapse (ω e)) false x y=1

abbrev RawNeighbourTestIndex (V:Type):Type:=Option (V⊕V⊕(V×V))

def rawApproxNeighbourTestSet {V:Type} [Fintype V] [LinearOrder V]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool):RawNeighbourTestIndex V→Finset V
  | none=>Finset.univ
  | some (.inl x)=>directedOutNeighbours (rawApproxPhysicalRelation P π d ω) x
  | some (.inr (.inl y))=>directedInNeighbours (rawApproxPhysicalRelation P π d ω) y
  | some (.inr (.inr (x,y)))=>directedOutNeighbours (rawApproxPhysicalRelation P π d ω) x ∩
      directedInNeighbours (rawApproxPhysicalRelation P π d ω) y

theorem raw_neighbour_test_index_card_bound {V:Type} [Fintype V] (hn:0<Fintype.card V):
    Fintype.card (RawNeighbourTestIndex V)≤4*(Fintype.card V)^2:=by
  simp only [RawNeighbourTestIndex,Fintype.card_option,Fintype.card_sum,Fintype.card_prod]
  nlinarith

theorem raw_unassigned_physical_neighbour_tests_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let law:=rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    let μ:=FiniteLaw.pi law
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      ∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawApproxNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawApproxNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<
          (Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN⟩:=raw_unassigned_physical_adaptive_high_probability d hd δ hδ
  refine ⟨max N 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hU P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν law μ f
  have hn0:0<Fintype.card V:=by omega
  exact hN V (by omega) U Γ Color (RawNeighbourTestIndex V) hU (raw_neighbour_test_index_card_bound hn0)
    π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (rawApproxNeighbourTestSet P π d) F ν
end Oberwolfach
