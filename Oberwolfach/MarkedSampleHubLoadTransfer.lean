module

public import Oberwolfach.MarkedPotentialSpokeAtHub
public import Oberwolfach.MarkedHubFixedWeightRestriction
public import Oberwolfach.MarkedLocalLoadSpokeChanges
public import Oberwolfach.MarkedSampleArcs

@[expose] public section

/-! The actual sampled hub degree equals the parent spoke potential at
that hub. The spoke root remains omitted until its membership is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_hub_load_transfer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (u:U) (hdis:∀ v,¬(H false v u∧H true v u))
    (j:Bool) (v:V) (hv:H j v u):
    hypergraphWeightedDegree
      (hubMarkedCycleVertices
        (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
        (head:=fun e=>e.val.2)
        (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
        (khead:=fun e=>e.val.2) (m:=m) (π:=π) (b:=3*d) (H₀:=H false) (Hₖ:=H true) u)
      (fun C=>weight C.val/(D*p^m*k*s₀^m)) v=
    typedMarkedPotentialLoad
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
          (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m))
      (rawMarkedPairRims P π d σ) H (Sum.inr (j,v,u)):=by
  have he:=hub_marked_degree_eq_omitted
    (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (head:=fun e=>e.val.2)
    (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (khead:=fun e=>e.val.2)
    (m:=m) (π:=π) (b:=3*d) u hdis (fun C=>weight C.val/(D*p^m*k*s₀^m)) j v
    (by cases j <;> simpa using hv)
  simp only [hubCycleAsMarked] at he
  rw [he]
  rw [marked_full_potential_spoke (tail:=Prod.fst) (head:=Prod.snd) (ktail:=Prod.fst) (khead:=Prod.snd)
    (m:=m) (π:=π) (b:=3*d) (fun C=>weight C.val/(D*p^m*k*s₀^m))]
  let PE:=fun e:V×V=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false e.1 e.2=1
  let PK:=fun e:V×V=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true e.1 e.2=1
  have hh:=marked_restricted_typed_root_load (tail:=Prod.fst) (head:=Prod.snd)
    (ktail:=Prod.fst) (khead:=Prod.snd) (m:=m) (π:=π) (b:=3*d) PE PK
    (fun _ _ h=>h) (fun _ _ h=>h) (fun C=>weight C.val/(D*p^m*k*s₀^m))
    (fun x:Bool×V=>if x.1 then H true x.2 u else H false x.2 u) (j,v)
  convert hh using 1 <;> first | rfl |
    (apply Finset.sum_congr (by ext;simp)
     intro C _
     congr 1
     apply propext
     constructor <;> rintro ⟨hr,hR,hH⟩ <;> refine ⟨hr,hR,?_⟩ <;>
       rintro ⟨b,x⟩ hx hne <;> have h:=hH (b,x) hx hne <;> cases b <;> simpa using h)

theorem marked_sample_hub_degree_error
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀ ε:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (hload:MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight ε σ H)
    (u:U) (hdis:∀ v,¬(H false v u∧H true v u)) (v:V) (hv:H false v u∨H true v u):
    |1-hypergraphWeightedDegree
      (hubMarkedCycleVertices
        (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
        (head:=fun e=>e.val.2)
        (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
        (khead:=fun e=>e.val.2) (m:=m) (π:=π) (b:=3*d) (H₀:=H false) (Hₖ:=H true) u)
      (fun C=>weight C.val/(D*p^m*k*s₀^m)) v|≤ε:=by
  rcases hv with hv|hv
  · rw [marked_sample_hub_load_transfer P π d m D p k s₀ weight σ H u hdis false v hv,abs_sub_comm]
    exact hload (false,v,u)
  · rw [marked_sample_hub_load_transfer P π d m D p k s₀ weight σ H u hdis true v hv,abs_sub_comm]
    exact hload (true,v,u)

end Oberwolfach
