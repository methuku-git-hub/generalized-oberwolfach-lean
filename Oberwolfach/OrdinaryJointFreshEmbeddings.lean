module

public import Oberwolfach.OrdinaryFreshPairEmbeddings
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! Joint embeddings of finitely many different finite graph pairs. The
single-pair existence input is used after adding every earlier row and hub
label to the forbidden sets. Thus all cross-separation conclusions hold on
one family of embeddings, rather than on separately chosen witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_joint_fresh_embeddings (l M:ℕ)
    (Vd Ud:Fin l→Type) [∀ i,Fintype (Vd i)] [∀ i,Fintype (Ud i)]
    [∀ i,DecidableEq (Vd i)] [∀ i,DecidableEq (Ud i)]
    (G:∀ i,SimpleGraph (Vd i)) (Hs:∀ i,Vd i→Ud i→Prop)
    (Q F:SimpleGraph V) (H:V→U→Prop) (A W R:Finset V) (B:Finset U)
    (hV:∀ i,Fintype.card (Vd i)≤M) (hU:∀ i,Fintype.card (Ud i)≤M)
    (hchoose:∀ (R':Finset V) (B':Finset U),R⊆R'→B⊆B'→
      R'.card≤R.card+l*M→B'.card≤B.card+l*M→∀ i:Fin l,
      ∃ e:OrdinaryPairHostEmbedding (G i) (Hs i) Q H,e.IsFresh F A W R' B') :
    ∃ e:∀ i,OrdinaryPairHostEmbedding (G i) (Hs i) Q H,
      (∀ i,(e i).IsFresh F A W R B)∧
      (∀ i j,i≠j→∀ v:Vd i,∀ w:Vd j,(e i).row v≠(e j).row w)∧
      (∀ i j,i≠j→∀ u:Ud i,∀ u':Ud j,(e i).hub u≠(e j).hub u')∧
      (∀ i j,i≠j→∀ v:Vd i,∀ w:Vd j,¬F.Adj ((e i).row v) ((e j).row w)) := by
  let C:=Option (Σ i:Fin l,OrdinaryPairHostEmbedding (G i) (Hs i) Q H)
  let rows:C→Finset V:=fun c=>c.elim ∅ (fun p=>Finset.univ.image p.2.row)
  let hubs:C→Finset U:=fun c=>c.elim ∅ (fun p=>Finset.univ.image p.2.hub)
  let allowed:=fun (i:Fin l) (c:C)=>∃ e:OrdinaryPairHostEmbedding (G i) (Hs i) Q H,
    c=some ⟨i,e⟩∧e.IsFresh F A W R B
  let compatible:=fun (c c':C)=>Disjoint (rows c) (rows c')∧Disjoint (hubs c) (hubs c')∧
    ∀ v∈rows c,∀ w∈rows c',¬F.Adj v w
  obtain ⟨chosen,hchosen,hcomp⟩:=sequential_select_prefix l allowed compatible none (by
    intro i chosen hp
    let s:=Finset.univ.filter (fun j:Fin l=>j.val < i.val)
    let R':=R∪s.biUnion (fun j=>rows (chosen j))
    let B':=B∪s.biUnion (fun j=>hubs (chosen j))
    have hsc:s.card≤l:=by simpa using Finset.card_le_univ s
    have hrc:(s.biUnion (fun j=>rows (chosen j))).card≤l*M:=by
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _j∈s,M := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨e,he,hfresh⟩:=hp.2.1 j (Finset.mem_filter.mp hj).2
          rw [he]
          exact Finset.card_image_le.trans ((Finset.card_univ).trans_le (hV j))
        _ = s.card*M := by simp
        _ ≤ l*M := Nat.mul_le_mul_right _ hsc
    have hbc:(s.biUnion (fun j=>hubs (chosen j))).card≤l*M:=by
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _j∈s,M := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨e,he,hfresh⟩:=hp.2.1 j (Finset.mem_filter.mp hj).2
          rw [he]
          exact Finset.card_image_le.trans ((Finset.card_univ).trans_le (hU j))
        _ = s.card*M := by simp
        _ ≤ l*M := Nat.mul_le_mul_right _ hsc
    obtain ⟨e,hfresh⟩:=hchoose R' B' Finset.subset_union_left Finset.subset_union_left
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hrc _))
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hbc _)) i
    refine ⟨some ⟨i,e⟩,⟨e,rfl,?_,(fun a h=>hfresh.2.1 a (Finset.mem_union_left _ h)),hfresh.2.2⟩,?_⟩
    · intro a
      exact ⟨(hfresh.1 a).1,(hfresh.1 a).2.1,
        fun h=>(hfresh.1 a).2.2.1 (Finset.mem_union_left _ h),
        fun z hz=>(hfresh.1 a).2.2.2 z (Finset.mem_union_left _ hz)⟩
    · intro j hj
      have hjS:j∈s:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
      have hrj:rows (chosen j)⊆R':=fun _ h=>Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hjS,h⟩)
      have hbj:hubs (chosen j)⊆B':=fun _ h=>Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hjS,h⟩)
      refine ⟨?_,?_,?_⟩
      · apply Finset.disjoint_left.mpr
        intro v hv hv'
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv'
        exact (hfresh.1 a).2.2.1 (hrj hv)
      · apply Finset.disjoint_left.mpr
        intro u hu hu'
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hu'
        exact hfresh.2.1 a (hbj hu)
      · intro v hv w hw
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hw
        exact fun h=>(hfresh.1 a).2.2.2 v (hrj hv) h.symm)
  choose e he hfresh using hchosen
  refine ⟨e,hfresh,?_,?_,?_⟩
  · intro i j hij v w heq
    have hsymm (i j:Fin l) (hij:i.val < j.val):Disjoint (rows (chosen i)) (rows (chosen j)):=(hcomp i j hij).1
    have hd:Disjoint (rows (chosen i)) (rows (chosen j)):=by
      rcases lt_or_gt_of_ne hij with h|h
      · exact hsymm i j h
      · exact (hsymm j i h).symm
    rw [he i,he j] at hd
    apply Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
    exact Finset.mem_image.mpr ⟨w,Finset.mem_univ _,heq.symm⟩
  · intro i j hij u u' heq
    have hd:Disjoint (hubs (chosen i)) (hubs (chosen j)):=by
      rcases lt_or_gt_of_ne hij with h|h
      · exact (hcomp i j h).2.1
      · exact (hcomp j i h).2.1.symm
    rw [he i,he j] at hd
    apply Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩)
    exact Finset.mem_image.mpr ⟨u',Finset.mem_univ _,heq.symm⟩
  · intro i j hij v w
    rcases lt_or_gt_of_ne hij with hij|hji
    · have hh:=(hcomp i j hij).2.2
      rw [he i,he j] at hh
      exact hh _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩) _ (Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩)
    · have hh:=(hcomp j i hji).2.2
      rw [he i,he j] at hh
      exact fun h=>hh _ (Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩) _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩) h.symm

end Oberwolfach
