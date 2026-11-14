module

public import Oberwolfach.MarkedInnerDomainSpokeWheel
public import Oberwolfach.MarkedInnerExtensionRimDeletion
public import Oberwolfach.MarkedSpokeAfterDeletion

@[expose] public section

/-! The inner-domain wheel constructor after actual physical rim deletion.
The returned wheel is in the original host and avoids the deleted rims. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_inner_spoke_wheel_after_deletion
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l) (X W:Finset V) (v:V) (u:U) (j:Bool) (c:ℝ)
    (hroot:if j then HK v u else H₀ v u)
    (hstep:∀ t x,c≤((X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧
      (if t then HK z u else H₀ z u))).card:ℝ))
    (hjoin:∀ t x y,x≠(if t then π y else y)→c≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead t z y∧H₀ z u)).card:ℝ))
    (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ x,(D.degree x:ℝ)≤δ)
    (hbudget:(W.card:ℝ)+(l+5)*(2*b+1)+2*δ<c):
    ∃ C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      C.2.val=u∧v∈markedWheelRows C∧Disjoint (markedWheelRimGraph C) D∧
      ∀ x∈markedWheelRows C,x=v∨(x∈X∧x∉W):=by
  let PE:=fun e:E=>¬D.Adj (tail e) (head e)
  let PK:=fun e:K=>¬D.Adj (ktail e) (π (khead e))
  obtain ⟨hs,hj⟩:=marked_inner_extension_counts_after_rim_deletion tail head ktail khead H₀ HK π X u c hstep hjoin D δ hδ hD
  obtain ⟨p,C,hCu,hcoord,hp,hsep⟩:=marked_spoke_wheel_on_inner_domain
    (fun e:{e:E//PE e}=>tail e.val) (fun e=>head e.val)
    (fun e:{e:K//PK e}=>ktail e.val) (fun e=>khead e.val) H₀ HK π b l hl X W v u j (c-2*δ)
    hroot hs hj (by linarith only [hbudget])
  let C':=markedWheelToLarger PE PK (fun _ _ h=>h) (fun _ _ h=>h) C
  have hrows:markedWheelRows C'=insert v (Finset.univ.image p):=by
    change Finset.univ.image C.1.val=_
    have he:C.1.val=rootedCycleOrder (markedRootOrder (l+3) j) v p:=funext hcoord
    rw [he]
    exact rootedCycleOrder_vertices _ _ _
  refine ⟨C',hCu,?_,?_,?_⟩
  · rw [hrows];exact Finset.mem_insert_self _ _
  · apply disjoint_iff_inf_le.mpr
    intro x y hxy
    have he:({x,y}:Finset V)∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b C'.1:=hxy.1.2
    change _∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b (markedCycleToLarger PE PK C.1) at he
    rw [markedCycleToLarger_physical] at he
    exact (marked_cycle_rim_avoids_deleted_graph D C.1 x y he hxy.2).elim
  · intro x hx
    rw [hrows] at hx
    rcases Finset.mem_insert.mp hx with he|he
    · exact Or.inl he
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
      exact Or.inr ⟨(hp i).1,(hp i).2.1⟩
end Oberwolfach
