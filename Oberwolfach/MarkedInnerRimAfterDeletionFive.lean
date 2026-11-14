module

public import Oberwolfach.MarkedInnerDomainRimWheelFive
public import Oberwolfach.MarkedInnerDomainRimWheel
public import Oberwolfach.MarkedInnerExtensionRimDeletion
public import Oberwolfach.MarkedPrescribedRimGeometry

@[expose] public section

/-! Complete a prescribed rim arc at its chosen hub after physical rim
deletion. Free vertices remain in the original inner counting domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_inner_rim_wheel_after_deletion_five
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b:ℕ) (X W:Finset V) (v w:V) (u:U) (j:Bool) (c:ℝ)
    (hvw:¬PermutationClose π b v w)
    (hroot:markedArcPresent tail head ktail khead j v w)
    (hv:H₀ v u) (hw:if j then HK w u else H₀ w u)
    (hstep:∀ t x,c≤((X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧
      (if t then HK z u else H₀ z u))).card:ℝ))
    (hjoin:∀ t x y,x≠(if t then π y else y)→c≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead t z y∧H₀ z u)).card:ℝ))
    (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ x,(D.degree x:ℝ)≤δ)
    (hrootD:¬D.Adj v (if j then π w else w))
    (hbudget:(W.card:ℝ)+((1:ℕ)+6)*(2*b+1)+2*δ<c):
    ∃ p:Fin ((1:ℕ)+3)↪V,∃ C:MarkedWheel tail head ktail khead ((1:ℕ)+4) π b H₀ HK,
      C.2.val=u∧(∀ i,C.1.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i))∧
      (∀ i,p i∈X∧p i∉W)∧Disjoint (markedWheelRimGraph C) D:=by
  let l:ℕ:=1
  let PE:=fun e:E=>¬D.Adj (tail e) (head e)
  let PK:=fun e:K=>¬D.Adj (ktail e) (π (khead e))
  obtain ⟨hs,hj⟩:=marked_inner_extension_counts_after_rim_deletion tail head ktail khead H₀ HK π X u c hstep hjoin D δ hδ hD
  have hr:markedArcPresent (fun e:{e:E//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K//PK e}=>ktail e.val) (fun e=>khead e.val) j v w:=
    (marked_arc_physical_restriction D j v w).mpr ⟨hroot,hrootD⟩
  obtain ⟨p,C,hCu,hcoord,hp,hsep⟩:=marked_rim_wheel_on_inner_domain_five
    (fun e:{e:E//PE e}=>tail e.val) (fun e=>head e.val)
    (fun e:{e:K//PK e}=>ktail e.val) (fun e=>khead e.val) H₀ HK π b X W v w u j (c-2*δ)
    hvw hr hv hw hs hj (by linarith only [hbudget])
  let C':=markedWheelToLarger PE PK (fun _ _ h=>h) (fun _ _ h=>h) C
  refine ⟨p,C',hCu,hcoord,fun i=>⟨(hp i).1,(hp i).2.1⟩,?_⟩
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  have he:({x,y}:Finset V)∈markedCyclePhysicalEdges tail head ktail khead (l+4) π b C'.1:=hxy.1.2
  change _∈markedCyclePhysicalEdges tail head ktail khead (l+4) π b (markedCycleToLarger PE PK C.1) at he
  rw [markedCycleToLarger_physical] at he
  exact (marked_cycle_rim_avoids_deleted_graph D C.1 x y he hxy.2).elim
end Oberwolfach
