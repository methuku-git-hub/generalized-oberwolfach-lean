module

public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.ColourDegrees
public import Oberwolfach.PermutationNeighbourCounts

@[expose] public section

/-! Restricted ordinary and marked in/out degrees, at any ambient root.
The domain is fixed before the physical exposure. Every summand refers to
one actual physical coordinate; the incoming marked centre uses pi(x). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

def markedDegreeEndpoints (π : Equiv.Perm V) (mark incoming : Bool) (x y : V) : V×V :=
  if incoming then (y,if mark then π x else x) else (x,if mark then π y else y)

def markedDegreeDomain (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (mark incoming : Bool) (x : V) (A : Finset V) : Finset V :=
  A.filter (fun y=>¬PermutationClose π b x y ∧
    P.Adj (markedDegreeEndpoints π mark incoming x y).1 (markedDegreeEndpoints π mark incoming x y).2)

def markedRestrictedDegree (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (mark incoming : Bool) (x : V) (A : Finset V) : ℕ :=
  ∑ y∈A,markedPhysicalRim P π b σ mark (if incoming then y else x) (if incoming then x else y)

theorem markedDegreeEdge_injective (π : Equiv.Perm V) (mark incoming : Bool) (x : V) :
    Function.Injective (fun y=>s((markedDegreeEndpoints π mark incoming x y).1,
      (markedDegreeEndpoints π mark incoming x y).2)) := by
  cases mark <;> cases incoming
  · exact incidentPair_injective x
  · intro y z h
    change s(y,x)=s(z,x) at h
    exact incidentPair_injective x (Sym2.eq_swap.trans (h.trans Sym2.eq_swap))
  · intro y z h
    exact π.injective (incidentPair_injective x h)
  · intro y z h
    change s(y,π x)=s(z,π x) at h
    exact incidentPair_injective (π x) (Sym2.eq_swap.trans (h.trans Sym2.eq_swap))

theorem markedRestrictedDegree_patterns (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (mark incoming : Bool) (x : V) (A : Finset V) :
    (markedRestrictedDegree P π b σ mark incoming x A:ℝ)=
      ∑ y∈markedDegreeDomain P π b mark incoming x A,
        patternValue {s((markedDegreeEndpoints π mark incoming x y).1,
          (markedDegreeEndpoints π mark incoming x y).2)}
          (fun _=>some (mark,orientationBit (markedDegreeEndpoints π mark incoming x y).1
            (markedDegreeEndpoints π mark incoming x y).2)) σ := by
  simp only [markedRestrictedDegree,markedDegreeDomain,Finset.sum_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro y hy
  cases mark <;> cases incoming <;>
    simp [markedDegreeEndpoints,markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation,
      patternValue,permutationClose_symm π b] <;> split_ifs <;> simp_all

theorem markedRestrictedDegree_tail (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (mark incoming : Bool) (x : V) (A : Finset V) (t : ℝ) (ht : 0≤t) :
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>t≤|(markedRestrictedDegree P π b σ mark incoming x A:ℝ)-
        (if mark then k else p)*(markedDegreeDomain P π b mark incoming x A).card|)≤
      2*Real.exp (-2*t^2/A.card) := by
  let ends := markedDegreeEndpoints π mark incoming x
  have hh := finiteLaw_singleton_patterns_tail_at_scale
    (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
    (markedDegreeDomain P π b mark incoming x A) (fun y=>s((ends y).1,(ends y).2))
    (fun y _=>some (mark,orientationBit (ends y).1 (ends y).2))
    (fun y hy z hz h=>markedDegreeEdge_injective π mark incoming x h)
    (n:=(A.card:ℝ)) (by exact_mod_cast Finset.card_filter_le A _) ht
  have hmass (y : V) : (markedPhysicalLaw p k hp hk hsum).mass
      (some (mark,orientationBit (ends y).1 (ends y).2))=if mark then k else p := by cases mark <;> rfl
  simp only [hmass,Finset.sum_const,nsmul_eq_mul] at hh
  dsimp [ends] at hh
  simpa only [← markedRestrictedDegree_patterns P π b, mul_comm] using hh

end Oberwolfach
