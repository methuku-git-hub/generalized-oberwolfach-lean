module

public import Oberwolfach.OrdinaryMatchingCycleMassByClass
public import Oberwolfach.MatchingClassMassUpper
public import Oberwolfach.OrdinaryAssignedRetainedHubTests

@[expose] public section
/-! The retained class-frequency tests yield a lower bound on the actual
selected cycle mass at each hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_matching_cycle_mass_upper
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (err:ℝ)
    (hzero:∀i:Fin K,¬θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i→
      (L.filter (fun x=>x.val.1=some i ∧ ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=u)).card=0)
    (hcount:∀z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ,
      |((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*
        ((L.filter (fun x=>x.val.1=some z.val.1 ∧ ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=z.val.2)).card:ℝ)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n|≤
        err*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n):
    let T:=Finset.univ.filter (fun i:Fin K=>θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i);
    ((∑a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)):ℝ)≤
      (1-θ+err)*(n:ℝ)*(∑i∈T,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i):=by
  intro T
  let len:=fun i:Fin K=>longPaddedSeedExponent i+2
  let count:=fun i:Fin K=>(L.filter (fun x=>x.val.1=some i ∧
    ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=u)).card
  let f:=fun i:Fin K=>ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i
  have hdev:∀i∈T,|((len i:ℝ)*(count i:ℝ))-(1-θ)*f i*n|≤err*f i*n:=by
    intro i hi
    let z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ:=⟨(i,u),(Finset.mem_filter.mp hi).2⟩
    exact hcount z
  have hz:∀i,i∉T→count i=0:=by
    intro i hi
    apply hzero i
    intro hret
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hret⟩
  have hh:=matching_class_mass_upper T len count f n θ err hz hdev
  have heq:=ordinary_matching_cycle_mass_by_class π d m RM state L u i₀
  have hsum : (∑i:Fin K, (len i:ℝ)*(count i:ℝ)) =
      ((∑i:Fin K, count i * len i):ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hh
  have heq' : (∑i:Fin K,count i * len i) =
      ∑a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2) := by
    dsimp [count,len]
    exact heq.symm
  have hconvert : (∑i:Fin K, (count i:ℝ) * (len i:ℝ)) =
      ∑a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        ((longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2:ℕ):ℝ) := by
    exact_mod_cast heq'
  rw [hconvert] at hh
  simpa only [f,Nat.cast_add,Nat.cast_ofNat] using hh
end Oberwolfach
