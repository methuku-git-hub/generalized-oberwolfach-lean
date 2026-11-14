module

public import Oberwolfach.OrdinaryRootedWheelEmbedding
public import Oberwolfach.OrdinaryWheelDisjointness
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! Simultaneous wheel attachments at prescribed rim roots. New rim
vertices are distinct between attachments; a prescribed root may repeat.
The spoke-density constant depends only on r, before all size bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_wheel_attachments (β : ℝ) (hβ : 0 < β) (r q N : ℕ) (hr : 3 ≤ r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (V U : Type*) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) →
    (∀ v,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ) ≤ (Finset.univ.filter (fun u => H v u)).card) →
    ∀ (R : Finset V) (B : Finset U) (x : Fin N → V),R.card ≤ q → (∀ i,x i∈R) →
    2*(B.card+N) < Fintype.card U →
    ∃ W : Fin N → OrdinaryWheel G ⊥ H r,
      (∀ i,x i∈(ordinaryWheelRim (W i)).support ∧ ordinaryWheelHub (W i)∉B ∧
        ∀ v∈(ordinaryWheelRim (W i)).support,v∈R → v=x i) ∧
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j)) ∧
        ordinaryWheelHub (W i)≠ordinaryWheelHub (W j) ∧
        ∀ v,v∈(ordinaryWheelRim (W i)).support → v∈(ordinaryWheelRim (W j)).support → v∈R) := by
  obtain ⟨n₀,hembed⟩ := ordinary_rooted_wheel_embedding β hβ r (q+N*r) hr
  refine ⟨n₀,?_⟩
  intro n hn V U _ _ _ _ hV G H hdeg hH R B x hR hx hB
  let allowed := fun i (o : Option (OrdinaryWheel G ⊥ H r)) =>
    ∃ W,o=some W ∧ x i∈(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∉B ∧
      ∀ v∈(ordinaryWheelRim W).support,v∈R → v=x i
  let compatible := fun (o p : Option (OrdinaryWheel G ⊥ H r)) =>
    ∀ W Z,o=some W → p=some Z →
      Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z) ∧
      ordinaryWheelHub W≠ordinaryWheelHub Z ∧
      ∀ v,v∈(ordinaryWheelRim W).support → v∈(ordinaryWheelRim Z).support → v∈R
  obtain ⟨F,hF,hcomp⟩ := sequential_select_prefix N allowed compatible none (by
    intro i F hprefix
    let J := Finset.univ.filter (fun j : Fin N => j.val < i.val)
    let A := R∪J.biUnion (fun j => optionWheelRimSupport (F j))
    let B' := B∪J.biUnion (fun j => optionWheelHubSet (F j))
    have hJ : J.card ≤ N := (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)
    have hAc : A.card ≤ q+N*r := by
      have hsum : (J.biUnion (fun j => optionWheelRimSupport (F j))).card ≤ J.card*r := by
        calc
          _ ≤ ∑ j∈J,(optionWheelRimSupport (F j)).card := Finset.card_biUnion_le
          _ ≤ ∑ _j∈J,r := Finset.sum_le_sum (fun j _ => optionWheelRimSupport_card (F j))
          _ = _ := by simp
      have hu := Finset.card_union_le R (J.biUnion (fun j => optionWheelRimSupport (F j)))
      dsimp [A]
      nlinarith
    have hBc : B'.card ≤ B.card+N := by
      have hsum : (J.biUnion (fun j => optionWheelHubSet (F j))).card ≤ J.card := by
        calc
          _ ≤ ∑ j∈J,(optionWheelHubSet (F j)).card := Finset.card_biUnion_le
          _ ≤ ∑ _j∈J,1 := Finset.sum_le_sum (fun j _ => optionWheelHubSet_card (F j))
          _ = _ := by simp
      have hu := Finset.card_union_le B (J.biUnion (fun j => optionWheelHubSet (F j)))
      dsimp [B']
      omega
    obtain ⟨W,hxW,huW,havoid⟩ := hembed n hn V U hV G H hdeg hH (x i) (A.erase (x i)) B'
      ((Finset.card_erase_le).trans hAc) (Finset.notMem_erase _ _) (by omega)
    have hroot (v : V) (hv : v∈(ordinaryWheelRim W).support) (hva : v∈A) : v=x i := by
      by_contra hne
      exact havoid v hv (Finset.mem_erase.mpr ⟨hne,hva⟩)
    refine ⟨some W,?_,?_⟩
    · refine ⟨W,rfl,hxW,?_,?_⟩
      · exact fun h => huW (Finset.mem_union_left _ h)
      · intro v hv hvr
        exact hroot v hv (Finset.mem_union_left _ hvr)
    · intro j hj
      intro Z W' hZ hW'
      have hW'val : W=W' := Option.some.inj hW'
      subst W'
      have hjJ : j∈J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
      have hcommon (v : V) (hvZ : v∈(ordinaryWheelRim Z).support)
          (hvW : v∈(ordinaryWheelRim W).support) : v=x i := by
        apply hroot v hvW
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨j,hjJ,?_⟩
        rw [hZ]
        exact Set.mem_toFinset.mpr hvZ
      have hhubs : ordinaryWheelHub Z≠ordinaryWheelHub W := by
        intro he
        apply huW
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨j,hjJ,?_⟩
        rw [hZ]
        simpa only [optionWheelHubSet,Option.elim_some,Finset.mem_singleton] using he.symm
      refine ⟨ordinaryWheels_disjoint_at_one_root Z W (x i) hcommon hhubs,hhubs,?_⟩
      intro v hvZ hvW
      rw [hcommon v hvZ hvW]
      exact hx i)
  choose W hW using hF
  refine ⟨W,?_,?_⟩
  · exact fun i => (hW i).2
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hcomp i j h (W i) (W j) (hW i).1 (hW j).1
    · have hh := hcomp j i h (W j) (W i) (hW j).1 (hW i).1
      exact ⟨hh.1.symm,Ne.symm hh.2.1,fun v hv hj => hh.2.2 v hj hv⟩

end Oberwolfach
