module

public import Oberwolfach.MarkedHostGreedyChoices
public import Oberwolfach.MarkedTransformerPathWheels
public import Oberwolfach.MarkedWheelResources

@[expose] public section

/-! Construct a wheel containing a prescribed spoke from actual host
intersection counts. Every other row avoids the supplied forbidden set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_prescribed_spoke_extension
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (j:Bool) (v:V) (u:U) (hroot:if j then HK v u else H₀ v u)
    (W Z:Finset V) (hv:v∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+4)*(2*b+1)<c):
    ∃ C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      C.2.val=u∧Sum.inr (v,u)∈markedWheelPhysicalResources C∧
      ∀ x∈Finset.univ.image C.1.val,x≠v→x∉W∧x∉Z∧∀ z∈Z,¬PermutationClose π b x z:=by
  have ho:c≤((Finset.univ.filter (fun a=>(∃ e,tail e=v∧head e=a)∧
      (∃ e,tail e=v∧head e=a)∧H₀ a u∧H₀ a u)).card:ℝ):=by
    simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_singleton,and_self,
      and_assoc,and_self_left] using Q.outgoing false false v {u} (by simp)
  have hc:c≤((Finset.univ.filter (fun a=>(if j then
      (∃ e,ktail e=a∧khead e=v)∧(∃ e,ktail e=a∧khead e=v) else
      (∃ e,tail e=a∧head e=v)∧(∃ e,tail e=a∧head e=v))∧H₀ a u∧H₀ a u)).card:ℝ):=by
    have h:=Q.incoming j false v {u} (by simp)
    cases j <;> simpa only [markedArcPresent,Bool.false_eq_true,ite_false,ite_true,
      markedSpokesTo_singleton,and_self] using h
  have hs:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      (if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)∧
      (if t then HK a u∧HK a u else H₀ a u∧H₀ a u))).card:ℝ):=by
    intro t x
    have h:=Q.outgoing t t x {u} (by simp)
    cases t <;> simpa only [markedArcPresent,Bool.false_eq_true,ite_false,ite_true,
      markedSpokesTo_singleton,and_self] using h
  have hj:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧
      (∃ e,tail e=a∧head e=y)∧H₀ a u∧H₀ a u)).card:ℝ):=by
    intro x y hxy
    simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_singleton,and_self] using
      Q.twoStep false x y {u} hxy (by simp)
  obtain ⟨p,C,D,hCu,_,hC,_,hav,_⟩:=marked_transformer_path_wheels
    tail head ktail khead H₀ HK π b l hl v v u u j W Z hv hv c
    (by cases j <;> exact ⟨hroot,hroot⟩) ho hc hs hj hbudget
  have hr:Finset.univ.image C.1.val=insert v (Finset.univ.image p):=by
    have he:C.1.val=rootedCycleOrder (markedRootOrder (l+3) j) v p:=funext hC
    rw [he]
    exact rootedCycleOrder_vertices _ _ _
  refine ⟨C,hCu,?_,?_⟩
  · rw [markedWheelPhysicalResources_spoke,hCu,hr]
    exact ⟨rfl,Finset.mem_insert_self _ _⟩
  · intro x hx hne
    rw [hr] at hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ((Finset.mem_insert.mp hx).resolve_left hne)
    exact hav i

end Oberwolfach
