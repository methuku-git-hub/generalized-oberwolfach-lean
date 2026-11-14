module

public import Oberwolfach.MarkedHostGreedyChoices
public import Oberwolfach.MarkedTransformerRimCycles
public import Oberwolfach.MarkedPhysicalDeletionExtensions
public import Oberwolfach.MarkedCycleFreshHub
public import Oberwolfach.MarkedWheelFamilyLoads
public import Oberwolfach.MarkedPackingRimGraphs
public import Oberwolfach.MarkedRootArcIsolation

@[expose] public section

/-! Complete a prescribed typed rim arc after physical rim deletion.
A compatible hub is selected only after the cycle has been constructed;
its exclusions include every already used spoke on that actual cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_prescribed_rim_cycle
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (j:Bool) (v w:V) (hvw:¬PermutationClose π b v w)
    (hroot:markedArcPresent tail head ktail khead j v w) (W:Finset V)
    (hbudget:(W.card:ℝ)+(l+6)*(2*b+1)<c):
    ∃ p:Fin (l+3)↪V,∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      (∀ a,C.val a=Fin.cons (α:=fun _=>V) v (Fin.cons w p)
        (canonicalMarkedRotation (if j then 0 else 3) a))∧(∀ a,p a∉W):=by
  have ho:c≤((Finset.univ.filter (fun a=>(∃ e,tail e=w∧head e=a)∧(∃ e,tail e=w∧head e=a))).card:ℝ):=by
    simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_empty,and_true,and_self] using
      Q.outgoing false false w ∅ (by simp)
  have hc:c≤((Finset.univ.filter (fun a=>(∃ e,tail e=a∧head e=v)∧(∃ e,tail e=a∧head e=v))).card:ℝ):=by
    simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_empty,and_true,and_self] using
      Q.incoming false false v ∅ (by simp)
  have hs:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ):=by
    intro t x
    simpa only [markedArcPresent,markedSpokesTo_empty,and_true] using Q.outgoing t false x ∅ (by simp)
  have hj:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧(∃ e,tail e=a∧head e=y))).card:ℝ):=by
    intro x y hxy
    simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_empty,and_true] using
      Q.twoStep false x y ∅ hxy (by simp)
  have hZ:(({v,w}:Finset V).card:ℝ)≤2:=by exact_mod_cast Finset.card_le_two
  obtain ⟨p,C,D,hC,_,hav,_⟩:=marked_transformer_rim_cycles tail head ktail khead π b l hl
    v w v w j W {v,w} (by simp) (by simp) (by simp) (by simp) hvw hvw c
    (by cases j <;> exact ⟨hroot,hroot⟩) ho hc hs hj
    (by nlinarith only [hZ,hbudget,show (0:ℝ)≤2*b+1 by positivity])
  exact ⟨p,C,hC,fun a=>(hav a).1⟩

theorem marked_rim_wheel_after_deletion
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ a,(D.degree a:ℝ)≤δ)
    (j:Bool) (v w:V) (hvw:¬PermutationClose π b v w)
    (hroot:markedArcPresent tail head ktail khead j v w)
    (hrootD:¬D.Adj v (if j then π w else w)) (W:Finset V) (B:Finset U)
    (A:V→U→Prop) (L:ℕ) (hA:∀ a,(Finset.univ.filter (A a)).card≤L)
    (hbudget:(W.card:ℝ)+(l+6)*(2*b+1)+2*δ<c)
    (hbudgetU:(B.card:ℝ)+(l+5)*L<ch):
    ∃ p:Fin (l+3)↪V,∃ C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ a,C.1.val a=Fin.cons (α:=fun _=>V) v (Fin.cons w p)
        (canonicalMarkedRotation (if j then 0 else 3) a))∧
      (∀ a,p a∉W)∧C.2.val∉B∧(∀ a∈markedWheelRows C,¬A a C.2.val)∧
      Disjoint (markedWheelRimGraph C) D:=by
  let PE:=fun e:E=>¬D.Adj (tail e) (head e)
  let PK:=fun e:K=>¬D.Adj (ktail e) (π (khead e))
  have Q':=marked_host_extensions_after_rim_deletion Q D δ hδ hD
  have hr:markedArcPresent (fun e:{e:E // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // PK e}=>ktail e.val) (fun e=>khead e.val) j v w:=
    (marked_arc_physical_restriction D j v w).mpr ⟨hroot,hrootD⟩
  obtain ⟨p,C,hC,hp⟩:=marked_prescribed_rim_cycle Q' hl j v w hvw hr W (by linarith only [hbudget])
  let F:Finset U:=(Finset.univ.image C.val).biUnion (fun a=>Finset.univ.filter (A a))
  have hF:F.card≤(l+5)*L:=by
    apply Finset.card_biUnion_le.trans
    apply (Finset.sum_le_sum (fun a ha=>hA a)).trans
    have hc:(Finset.univ.image C.val).card=l+5:=by
      rw [Finset.card_image_of_injective _ (permutationSeparated_injective π b C.val C.property.1)]
      simp
    simp only [Finset.sum_const,smul_eq_mul,hc,le_refl]
  have hBF:((B∪F).card:ℝ)<ch:=by
    have hh:((B∪F).card:ℝ)≤B.card+((l+5)*L:ℕ):=by
      exact_mod_cast (Finset.card_union_le B F).trans (Nat.add_le_add_left hF _)
    push_cast at hh
    linarith only [hh,hbudgetU]
  obtain ⟨u,hu,hCu⟩:=marked_cycle_fresh_hub Q' C (B∪F) hBF
  let C':=markedWheelToLarger PE PK (fun _ _ h=>h) (fun _ _ h=>h) ⟨C,⟨u,hCu⟩⟩
  refine ⟨p,C',hC,hp,fun h=>hu (Finset.mem_union_left _ h),?_,?_⟩
  · intro a ha hAa
    apply hu
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAa⟩⟩)
  · apply disjoint_iff_inf_le.mpr
    intro x y hxy
    have he:({x,y}:Finset V)∈markedCyclePhysicalEdges tail head ktail khead (l+4) π b C'.1:=hxy.1.2
    change _∈markedCyclePhysicalEdges tail head ktail khead (l+4) π b (markedCycleToLarger PE PK C) at he
    rw [markedCycleToLarger_physical] at he
    exact (marked_cycle_rim_avoids_deleted_graph D C x y he hxy.2).elim

end Oberwolfach
