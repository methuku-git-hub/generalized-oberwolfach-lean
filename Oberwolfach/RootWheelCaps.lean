module

public import Oberwolfach.OrdinaryHubWheelPacking
public import Oberwolfach.InjectiveHubWheelDegrees

@[expose] public section

/-! Degree and saturation estimates for wheels sharing a row root.
The root is excluded from the degree cap; prescribed endpoints and
internal rim vertices are counted separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I : Type*} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q F : SimpleGraph V} {H : V→U→Prop} {r:ℕ}

def rootWheelInternal (C:OrdinaryWheel Q F H r) (x v w:V) : Finset V:=
  (ordinaryWheelRim C).support.toFinset\{x,v,w}

def rootWheelInternalLoad (C:I→OrdinaryWheel Q F H r) (x:V) (v w:I→V) (a:V) : ℕ:=
  (Finset.univ.filter (fun i=>a∈rootWheelInternal (C i) x (v i) (w i))).card

theorem rootWheelInternal_card (C:OrdinaryWheel Q F H r) (x v w:V) :
    (rootWheelInternal C x v w).card≤r:=
  (Finset.card_le_card Finset.sdiff_subset).trans_eq C.val.1.val.property.support_card

theorem rootWheelInternalLoad_total (C:I→OrdinaryWheel Q F H r) (x:V) (v w:I→V) :
    ∑ a,rootWheelInternalLoad C x v w a≤Fintype.card I*r:=by
  have he : ∑ a,rootWheelInternalLoad C x v w a=∑ i,(rootWheelInternal (C i) x (v i) (w i)).card:=by
    simp only [rootWheelInternalLoad,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  rw [he]
  calc
    _ ≤ ∑ _i:I,r:=Finset.sum_le_sum (fun i _=>rootWheelInternal_card (C i) x (v i) (w i))
    _ = _:=by simp

theorem rootWheelInternal_saturated (C:I→OrdinaryWheel Q F H r) (x:V) (v w:I→V) (K:ℕ) :
    K*(Finset.univ.filter (fun a=>K≤rootWheelInternalLoad C x v w a)).card≤Fintype.card I*r:=by
  calc
    _ = ∑ a∈Finset.univ.filter (fun a=>K≤rootWheelInternalLoad C x v w a),K:=by simp [Nat.mul_comm]
    _ ≤ ∑ a∈Finset.univ.filter (fun a=>K≤rootWheelInternalLoad C x v w a),rootWheelInternalLoad C x v w a:=
      Finset.sum_le_sum (fun a ha=>(Finset.mem_filter.mp ha).2)
    _ ≤ ∑ a,rootWheelInternalLoad C x v w a:=Finset.sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _)
    _ ≤ _:=rootWheelInternalLoad_total C x v w

theorem rootWheelFamily_degree (C:I→OrdinaryWheel Q F H r) (x:V) (v w:I→V) (K:ℕ)
    (hend:∀ a,(Finset.univ.filter (fun i=>a=v i∨a=w i)).card≤1)
    (hcap:∀ a,rootWheelInternalLoad C x v w a≤K)
    (a:V) (hax:a≠x) : (wheelFamilyRim C).degree a≤2*(K+1):=by
  have hc : (Finset.univ.filter (fun i=>a∈(ordinaryWheelRim (C i)).support.toFinset)).card≤K+1:=by
    have hs : Finset.univ.filter (fun i=>a∈(ordinaryWheelRim (C i)).support.toFinset)⊆
        (Finset.univ.filter (fun i=>a∈rootWheelInternal (C i) x (v i) (w i)))∪
        (Finset.univ.filter (fun i=>a=v i∨a=w i)):=by
      intro i hi
      have hai:=(Finset.mem_filter.mp hi).2
      by_cases he:a=v i∨a=w i
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
      · apply Finset.mem_union_left
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨hai,?_⟩⟩
        simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using ⟨hax,not_or.mp he⟩
    have hh:=(Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    exact hh.trans (Nat.add_le_add (hcap a) (hend a))
  have hh:=graph_iSup_global_degree_bound (fun i=>ordinaryWheelRim (C i))
    (fun i=>(ordinaryWheelRim (C i)).support.toFinset) 2
    (by intro i a b hab;exact ⟨Set.mem_toFinset.mpr hab.mem_support_left,Set.mem_toFinset.mpr hab.mem_support_right⟩)
    (by
      intro i a
      have hi:IsEmbeddedCycle (ordinaryWheelRim (C i)) r:=(C i).val.1.val.property
      rcases hi.degree_zero_or_two a with h|h <;> omega) a
  exact hh.trans (Nat.mul_le_mul_left 2 hc)

theorem ordinaryWheel_root_neighbors (C:OrdinaryWheel Q F H r) (x v w:V) (hvw:v≠w)
    (hxv:(ordinaryWheelRim C).Adj x v) (hxw:(ordinaryWheelRim C).Adj x w) :
    (ordinaryWheelRim C).neighborFinset x={v,w}:=by
  have hs : ({v,w}:Finset V)⊆(ordinaryWheelRim C).neighborFinset x:=by
    intro a ha
    rcases Finset.mem_insert.mp ha with he|he
    · rw [he];exact ((ordinaryWheelRim C).mem_neighborFinset x v).mpr hxv
    · rw [Finset.mem_singleton.mp he];exact ((ordinaryWheelRim C).mem_neighborFinset x w).mpr hxw
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  rw [SimpleGraph.card_neighborFinset_eq_degree,Finset.card_pair hvw]
  have hC:IsEmbeddedCycle (ordinaryWheelRim C) r:=C.val.1.val.property
  rcases hC.degree_zero_or_two x with h|h <;> omega


theorem disjoint_pairs_endpoint_count (v w:I→V)
    (hpair:∀ i j,i≠j → Disjoint ({v i,w i}:Finset V) {v j,w j}) (a:V) :
    (Finset.univ.filter (fun i=>a=v i∨a=w i)).card≤1:=by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  exact Finset.disjoint_left.mp (hpair i j hij)
    (by simpa only [Finset.mem_insert,Finset.mem_singleton] using (Finset.mem_filter.mp hi).2)
    (by simpa only [Finset.mem_insert,Finset.mem_singleton] using (Finset.mem_filter.mp hj).2)

theorem rootWheelInternalLoad_snoc {k:ℕ} (C:Fin k→OrdinaryWheel Q F H r)
    (B:OrdinaryWheel Q F H r) (x:V) (v w:Fin k→V) (a b z:V) :
    rootWheelInternalLoad (Fin.snoc C B) x (Fin.snoc v a) (Fin.snoc w b) z=
      rootWheelInternalLoad C x v w z+(if z∈rootWheelInternal B x a b then 1 else 0):=by
  simp only [rootWheelInternalLoad,Finset.card_filter,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]


end Oberwolfach
