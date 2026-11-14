module

public import Oberwolfach.MarkedCycleRestrictionByEndpoints
public import Oberwolfach.CommonWitnessTransfer

@[expose] public section

/-! The common-pair potential load is the root-omitted cycle load on the
actual sampled arc graph. Coefficients are unchanged and the root ranges
over the entire vertex set, whether or not it belongs to either class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem commonSelectedClass_typed_mem (H:Bool→V→U→Prop) (κ:V→Bool) (u u':U) (x:Bool×V):
    x∈typedClassSet (commonSelectedClass H κ u u' true) (commonSelectedClass H κ u u' false)↔
      commonThinnedSpokes H κ u u' x.1 x.2 ():=by
  rcases x with ⟨j,v⟩
  rw [typedClassSet_mem]
  cases j <;> simp only [ite_true,Bool.false_eq_true,ite_false,commonSelectedClass,
    Finset.mem_filter,Finset.mem_univ,true_and]

theorem marked_common_root_load_transfer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k sbar:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (κ:V→Bool) (u u':U) (j:Bool) (v:V):
    resourceRootOmittedLoad
      (typedMarkedCycleVertices (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
        (head:=fun e=>e.val.2) (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
        (khead:=fun e=>e.val.2) (m:=m) (π:=π) (b:=3*d))
      (fun C=>weight C.val/(D*p^m*k*sbar^m))
      (fun x=>x∈typedClassSet (commonSelectedClass H κ u u' true) (commonSelectedClass H κ u u' false)) (j,v)=
    typedMarkedPotentialLoad (H₀:=fun (_:V) (_:Unit)=>True) (Hₖ:=fun _ _=>True)
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
          (fun (_:V) (_:Unit)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*sbar^m))
      (rawMarkedPairRims P π d σ) (commonThinnedSpokes H κ u u') (Sum.inr (j,v,())):=by
  let PE:=fun e:V×V=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false e.1 e.2=1
  let PK:=fun e:V×V=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true e.1 e.2=1
  rw [marked_unit_potential_load (tail:=Prod.fst) (head:=Prod.snd) (ktail:=Prod.fst) (khead:=Prod.snd)
    (m:=m) (π:=π) (b:=3*d) (fun C=>weight C.val/(D*p^m*k*sbar^m))
    (rawMarkedPairRims P π d σ) (commonThinnedSpokes H κ u u') j v]
  have hh:=marked_restricted_typed_root_load (tail:=Prod.fst) (head:=Prod.snd)
    (ktail:=Prod.fst) (khead:=Prod.snd) (m:=m) (π:=π) (b:=3*d) PE PK
    (fun _ _ h=>h) (fun _ _ h=>h)
    (fun C=>weight C.val/(D*p^m*k*sbar^m))
    (fun x=>x∈typedClassSet (commonSelectedClass H κ u u' true) (commonSelectedClass H κ u u' false)) (j,v)
  convert hh using 1 <;> first | rfl |
    (apply Finset.sum_congr (by ext; simp)
     intro C _
     simp only [commonSelectedClass_typed_mem]
     rfl)

end Oberwolfach
