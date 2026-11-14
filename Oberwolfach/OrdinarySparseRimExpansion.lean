module

public import Oberwolfach.RootedPathCycleEmbedding
public import Oberwolfach.TransformerRimPaths

@[expose] public section

/-! The rim expansion in a common-neighbour host. Separation is proved
against every old row label even when the old labels are not separated
from each other. No minimum-degree condition is substituted for the
common-neighbour assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem sparse_rim_expansion_cycle (Q F : SimpleGraph V) (A W R : Finset V)
    (x y : V) (r : ℕ) (hr : 3≤r) (d c : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+r+6)*(d+1)<c) :
    ∃ f : Fin r ↪ V,
      (∀ i j,(SimpleGraph.cycleGraph r).Adj i j → Q.Adj (f i) (f j)) ∧
      Q.Adj y (f ⟨0,by omega⟩) ∧ Q.Adj x (f ⟨r-1,by omega⟩) ∧
      (∀ i j,¬F.Adj (f i) (f j)) ∧
      ∀ i,f i∈A ∧ f i∉W ∧ f i∉R ∧ ∀ v∈R,¬F.Adj (f i) v := by
  have hd1 : 0≤d+1 := by linarith
  have hrR : (0:ℝ)≤r := Nat.cast_nonneg _
  obtain ⟨a,haA,haW,haR,hya,_hya,haF⟩ := sparse_common_neighbour_avoiding Q F A W R y y d c hd hF
    (hcount y y) (by nlinarith only [hbudget,hd1,hrR])
  have hRa : ((insert a R).card:ℝ)≤R.card+1 := by exact_mod_cast Finset.card_insert_le a R
  obtain ⟨b,hbA,hbW,hbRa,hxb,hab,hbF⟩ := sparse_common_neighbour_avoiding Q F A W (insert a R) x a d c hd hF
    (hcount x a) (by nlinarith only [hbudget,hd1,hrR,hRa])
  have hbR : b∉R := fun h => hbRa (Finset.mem_insert_of_mem h)
  let D := R∪R.biUnion (fun v => F.neighborFinset v)
  let W' := W∪D
  let Z : Finset V := {a,b}
  have hZ : ∀ v∈Z,∀ w∈Z,¬F.Adj v w := by
    apply graph_independent_insert F ({b}:Finset V) a
    · intro v hv w hw
      rw [Finset.mem_singleton.mp hv,Finset.mem_singleton.mp hw]
      exact F.loopless.irrefl b
    · intro w hw h
      rw [Finset.mem_singleton.mp hw] at h
      exact hbF a (Finset.mem_insert_self _ _) h.symm
  have hW' : (W'.card:ℝ)≤W.card+(R.card:ℝ)*(d+1) := by
    have hD := forbidden_used_neighbours_card F R d hF
    have hh : (W'.card:ℝ)≤W.card+(D.card:ℝ) := by exact_mod_cast Finset.card_union_le W D
    exact hh.trans (by dsimp [D];linarith only [hD])
  have hZc : (Z.card:ℝ)≤2 := by
    have hh := Finset.card_insert_le a ({b}:Finset V)
    simp only [Finset.card_singleton] at hh
    exact_mod_cast hh
  have hrsub : ((r-1:ℕ):ℝ)≤r := by exact_mod_cast Nat.sub_le r 1
  obtain ⟨p,hp,hlen,hclass,hind,_hZp⟩ := sparse_fixed_length_forbidden_path Q F A W' Z a b
    hab.ne (by simp [Z]) (by simp [Z]) hZ (r-1) (by omega) d c hd hF hcount
    (by nlinarith only [hbudget,hW',hZc,hrsub,hd1])
  let f := pathCycleEmbedding p hp hlen
  refine ⟨f,pathCycleEmbedding_hom hr p hp hlen hab,?_,?_,?_,?_⟩
  · simpa only [f,pathCycleEmbedding_first] using hya
  · simpa only [f,pathCycleEmbedding_last (r:=r) (by omega) p hp hlen] using hxb
  · intro i j
    exact hind _ (p.getVert_mem_support _) _ (p.getVert_mem_support _)
  · intro i
    rcases hclass (f i) (p.getVert_mem_support _) with ha|hb|hrest
    · rw [ha];exact ⟨haA,haW,haR,haF⟩
    · rw [hb];exact ⟨hbA,hbW,hbR,fun v hv => hbF v (Finset.mem_insert_of_mem hv)⟩
    · have hnotW : f i∉W := fun h => hrest.2.1 (Finset.mem_union_left _ h)
      have hnotR : f i∉R := fun h => hrest.2.1
        (Finset.mem_union_right _ (Finset.mem_union_left _ h))
      refine ⟨hrest.1,hnotW,hnotR,?_⟩
      intro v hv hFiv
      apply hrest.2.1
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨v,hv,(F.mem_neighborFinset v (f i)).mpr hFiv.symm⟩))

end Oberwolfach
