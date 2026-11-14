module

public import Oberwolfach.MarkedAssignedRowCounts
public import Oberwolfach.MarkedBoundaryExtensionCounts
public import Oberwolfach.MarkedAssignedRowAfterDeletion

@[expose] public section

/-! Complete an assigned boundary path using candidates in the prescribed
inner set. The outside root is retained in the wheel but is excluded from
all new path positions. Only actual physical rim deletions are charged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b l:ℕ} {c:ℝ}

theorem marked_assigned_row_in_domain (X:Finset V)
    (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (hl:2≤l) (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ x,(D.degree x:ℝ)≤δ)
    (v a z:V) (u:U) (jin jout:Bool) (htypes:¬(jin=true∧jout=true))
    (W Z:Finset V) (hv:v∈Z) (haX:a∈X) (hzX:z∈X)
    (haW:a∉W) (hzW:z∉W) (haZ:a∉Z) (hzZ:z∉Z)
    (haz:¬PermutationClose π b a z)
    (haF:∀ x∈Z,¬PermutationClose π b a x) (hzF:∀ x∈Z,¬PermutationClose π b z x)
    (haH:if jout then HK a u else H₀ a u) (hzH:H₀ z u)
    (hroot:if jin then HK v u else H₀ v u)
    (hopen:markedArcPresent tail head ktail khead jout v a)
    (hclose:markedArcPresent tail head ktail khead jin z v)
    (hopenD:¬D.Adj v (if jout then π a else a)) (hcloseD:¬D.Adj z (if jin then π v else v))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(2*b+1)+2*δ<c):
    ∃ p:Fin (l+3)↪V,∃ C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      p 0=a∧p (Fin.last (l+2))=z∧C.2.val=u∧
      (∀ i,C.1.val i=Fin.cons (α:=fun _=>V) v p (markedAssignedRowOrder (l+3) jin jout i))∧
      (∀ i,p i∈X∧p i∉W∧p i∉Z∧∀ x∈Z,¬PermutationClose π b (p i) x)∧
      PermutationSeparated π b p∧Disjoint (markedWheelRimGraph C) D:=by
  let PE:=fun e:E=>¬D.Adj (tail e) (head e)
  let PK:=fun e:K=>¬D.Adj (ktail e) (π (khead e))
  let H₀':=fun x w=>(x∈X∨x=v)∧H₀ x w
  let HK':=fun x w=>(x∈X∨x=v)∧HK x w
  have Q':=marked_boundary_counts_after_rim_deletion π X c Q D δ hδ hD
  have hstep (j:Bool) (x:V):c-2*δ≤((Finset.univ.filter (fun y=>
      (if j then ∃ e:Subtype PK,ktail e.val=x∧khead e.val=y else ∃ e:Subtype PE,tail e.val=x∧head e.val=y)∧
      (if j then HK' y u else H₀' y u))).card:ℝ):=by
    apply le_trans (Q'.step j x u)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hyX,hy⟩:=Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases j <;> exact ⟨hy.1,Or.inl hyX,hy.2⟩
  have hjoin (x y:V) (hxy:x≠y):c-2*δ≤((Finset.univ.filter (fun z=>
      (∃ e:Subtype PE,tail e.val=x∧head e.val=z)∧(∃ e:Subtype PE,tail e.val=z∧head e.val=y)∧H₀' z u)).card:ℝ):=by
    apply le_trans (Q'.join x y u hxy)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzX,hz⟩:=Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz.1,hz.2.1,Or.inl hzX,hz.2.2⟩
  have ho:markedArcPresent (fun e:Subtype PE=>tail e.val) (fun e=>head e.val)
      (fun e:Subtype PK=>ktail e.val) (fun e=>khead e.val) jout v a:=
    (marked_arc_physical_restriction D jout v a).mpr ⟨hopen,hopenD⟩
  have hc:markedArcPresent (fun e:Subtype PE=>tail e.val) (fun e=>head e.val)
      (fun e:Subtype PK=>ktail e.val) (fun e=>khead e.val) jin z v:=
    (marked_arc_physical_restriction D jin z v).mpr ⟨hclose,hcloseD⟩
  have haH':if jout then HK' a u else H₀' a u:=by cases jout <;> exact ⟨Or.inl haX,haH⟩
  have hroot':if jin then HK' v u else H₀' v u:=by cases jin <;> exact ⟨Or.inr rfl,hroot⟩
  obtain ⟨p,C,hp0,hplast,hCu,hcoord,hav,hsep⟩:=marked_assigned_row_wheel_from_counts
    (π:=π) (b:=b) (l:=l) (c:=c-2*δ) hl v a z u jin jout htypes W Z hv haW hzW haZ hzZ haz haF hzF
    haH' ⟨Or.inl hzX,hzH⟩ hroot' ho hc (by intro j x;convert hstep j x using 1 <;> congr!)
    (by intro x y hxy;convert hjoin x y hxy using 1 <;> congr!) (by linarith only [hbudget])
  let C':=markedWheelToLarger PE PK (fun _ _ h=>h.2) (fun _ _ h=>h.2) C
  have hpX (i:Fin (l+3)):p i∈X:=by
    let j:Fin (l+4):=(markedAssignedRowOrder (l+3) jin jout).symm i.succ
    have hj:C.1.val j=p i:=by
      rw [hcoord]
      simp only [j,Equiv.apply_symm_apply,Fin.cons_succ]
    have hs':Sum.inr (p i,u)∈markedWheelPhysicalResources C:=
      (markedWheelPhysicalResources_spoke C (p i) u).mpr ⟨hCu,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩⟩
    have hh:=(markedWheelPhysicalResources_spoke_present C (p i) u hs').elim And.left And.left
    exact hh.resolve_right (fun he=>(hav i).2.1 (he ▸ hv))
  refine ⟨p,C',hp0,hplast,hCu,hcoord,fun i=>⟨hpX i,hav i⟩,hsep,?_⟩
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  have he:({x,y}:Finset V)∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b C'.1:=hxy.1.2
  change _∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b (markedCycleToLarger PE PK C.1) at he
  rw [markedCycleToLarger_physical] at he
  exact (marked_cycle_rim_avoids_deleted_graph D C.1 x y he hxy.2).elim

end Oberwolfach
