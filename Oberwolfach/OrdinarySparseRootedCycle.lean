module

public import Oberwolfach.RootedPathCycleEmbedding
public import Oberwolfach.TransformerRimPaths

@[expose] public section

/-! A rooted cycle from common-neighbour counts, with explicit losses for
forbidden labels and neighbours in the separation graph. The old root
set need not be independent in the separation graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem sparse_rooted_cycle_embedding (Q F : SimpleGraph V) (A W R : Finset V)
    (x : V) (hx : x∈R) (r : ℕ) (hr : 3≤r) (d c : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+r+5)*(d+1)<c) :
    ∃ f : Fin r ↪ V,f ⟨0,by omega⟩=x ∧
      (∀ i j,(SimpleGraph.cycleGraph r).Adj i j → Q.Adj (f i) (f j)) ∧
      (∀ i j,¬F.Adj (f i) (f j)) ∧
      ∀ i,i≠⟨0,by omega⟩ → f i∈A ∧ f i∉W ∧ f i∉R ∧ ∀ v∈R,¬F.Adj (f i) v := by
  have hd1 : 0≤d+1 := by linarith
  obtain ⟨y,hyA,hyW,hyR,hxy,_hxy,hyF⟩ := sparse_common_neighbour_avoiding Q F A W R x x d c hd hF
    (hcount x x) (by nlinarith only [hbudget,hd1,(show (0:ℝ)≤r from Nat.cast_nonneg _)])
  let D := R∪R.biUnion (fun v => F.neighborFinset v)
  let W' := W∪D
  let Z : Finset V := {x,y}
  have hZ : ∀ a∈Z,∀ b∈Z,¬F.Adj a b := by
    apply graph_independent_insert F ({y}:Finset V) x
    · intro a ha b hb
      have ha' : a=y := Finset.mem_singleton.mp ha
      have hb' : b=y := Finset.mem_singleton.mp hb
      rw [ha',hb']
      exact F.loopless.irrefl y
    · intro a ha h
      have ha' : a=y := Finset.mem_singleton.mp ha
      rw [ha'] at h
      exact hyF x hx h.symm
  have hW' : (W'.card:ℝ)≤W.card+(R.card:ℝ)*(d+1) := by
    have hD := forbidden_used_neighbours_card F R d hF
    have hh : (W'.card:ℝ)≤W.card+(D.card:ℝ) := by exact_mod_cast Finset.card_union_le W D
    exact hh.trans (by dsimp [D];linarith only [hD])
  have hZc : (Z.card:ℝ)≤2 := by
    have hh := Finset.card_insert_le x ({y}:Finset V)
    simp only [Finset.card_singleton] at hh
    exact_mod_cast hh
  have hrR : ((r-1:ℕ):ℝ)≤r := by exact_mod_cast Nat.sub_le r 1
  have hpbudget : W'.card+((Z.card:ℝ)+(r-1:ℕ))*(d+1)<c := by
    nlinarith only [hbudget,hW',hZc,hrR,hd1]
  obtain ⟨p,hp,hlen,hclass,hind,_hZp⟩ := sparse_fixed_length_forbidden_path Q F A W' Z x y
    hxy.ne (by simp [Z]) (by simp [Z]) hZ (r-1) (by omega) d c hd hF hcount hpbudget
  let f := pathCycleEmbedding p hp hlen
  have hf0 : f ⟨0,by omega⟩=x := pathCycleEmbedding_first _ p hp hlen
  refine ⟨f,hf0,pathCycleEmbedding_hom hr p hp hlen hxy,?_,?_⟩
  · intro i j
    exact hind _ (p.getVert_mem_support _) _ (p.getVert_mem_support _)
  · intro i hi
    have hfx : f i≠x := by intro he;exact hi (f.injective (he.trans hf0.symm))
    rcases hclass (f i) (p.getVert_mem_support _) with hx'|hy'|hrest
    · exact (hfx hx').elim
    · rw [hy']
      exact ⟨hyA,hyW,hyR,hyF⟩
    · have hnotW : f i∉W := fun h => hrest.2.1 (Finset.mem_union_left _ h)
      have hnotR : f i∉R := fun h => hrest.2.1
        (Finset.mem_union_right _ (Finset.mem_union_left _ h))
      refine ⟨hrest.1,hnotW,hnotR,?_⟩
      intro v hv hFiv
      apply hrest.2.1
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨v,hv,(F.mem_neighborFinset v (f i)).mpr hFiv.symm⟩))

end Oberwolfach
