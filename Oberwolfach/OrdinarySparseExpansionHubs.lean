module

public import Oberwolfach.OrdinarySparseRootedCycle
public import Oberwolfach.OrdinarySparseRimExpansion

@[expose] public section

/-! Complete rim and spoke replacements in a sparse relative host.
The hub choices use the common-neighbour lower bounds for separated
sets; no dense spoke-degree hypothesis is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem common_hub_from_count (H : V → U → Prop) (T : Finset V) (B : Finset U) (c : ℝ)
    (hcount : c≤((common Finset.univ T (fun v => Finset.univ.filter (H v))).card:ℝ))
    (hbudget : (B.card:ℝ)<c) : ∃ u,u∉B ∧ ∀ v∈T,H v u := by
  have hsize : B.card<(common Finset.univ T (fun v => Finset.univ.filter (H v))).card := by
    exact_mod_cast hbudget.trans_le hcount
  obtain ⟨u,hu,huB⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  exact ⟨u,huB,by simpa only [common,Finset.mem_filter,Finset.mem_univ,true_and] using hu⟩

theorem sparse_rim_expansion_embedding (Q F : SimpleGraph V) (H : V → U → Prop)
    (A W R : Finset V) (B : Finset U) (x y : V) (r : ℕ) (hr : 3≤r) (d c cH : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+r+6)*(d+1)<c)
    (hhub : ∀ T:Finset V,T.card≤r → (∀ v∈T,∀ w∈T,¬F.Adj v w) →
      cH≤((common Finset.univ T (fun v => Finset.univ.filter (H v))).card:ℝ))
    (hB : (B.card:ℝ)<cH) :
    ∃ (f : Fin r ↪ V) (u : U),
      (∀ i j,(SimpleGraph.cycleGraph r).Adj i j → Q.Adj (f i) (f j)) ∧
      (∀ i,H (f i) u) ∧ u∉B ∧
      Q.Adj y (f ⟨0,by omega⟩) ∧ Q.Adj x (f ⟨r-1,by omega⟩) ∧
      (∀ i j,¬F.Adj (f i) (f j)) ∧
      ∀ i,f i∈A ∧ f i∉W ∧ f i∉R ∧ ∀ v∈R,¬F.Adj (f i) v := by
  obtain ⟨f,hf,hy,hx,hind,havoid⟩ := sparse_rim_expansion_cycle Q F A W R x y r hr d c hd hF hcount hbudget
  let T := Finset.univ.image f
  have hTc : T.card≤r := Finset.card_image_le.trans (by simp)
  have hTF : ∀ v∈T,∀ w∈T,¬F.Adj v w := by
    intro v hv w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact hind i j
  obtain ⟨u,hu,hHu⟩ := common_hub_from_count H T B cH (hhub T hTc hTF) hB
  exact ⟨f,u,hf,(fun i => hHu _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)),hu,hy,hx,hind,havoid⟩

theorem sparse_spoke_expansion_embedding (Q F : SimpleGraph V) (H : V → U → Prop)
    (A W R : Finset V) (B : Finset U) (x : V) (u : U) (r : ℕ) (hr : 3≤r) (d c cH : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ u u' v w,c≤(((A.filter (fun a => H a u ∧ H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+r+6)*(d+1)<c)
    (hhub : ∀ T:Finset V,T.card≤r → (∀ v∈T,∀ w∈T,¬F.Adj v w) →
      cH≤((common Finset.univ T (fun v => Finset.univ.filter (H v))).card:ℝ))
    (hB : (B.card:ℝ)<cH) :
    ∃ (f : Fin r ↪ V) (u' : U),
      (∀ i j,(SimpleGraph.cycleGraph r).Adj i j → Q.Adj (f i) (f j)) ∧
      (∀ i,H (f i) u') ∧ u'∉B ∧ H x u' ∧ H (f ⟨0,by omega⟩) u ∧
      (∀ i j,¬F.Adj (f i) (f j)) ∧
      ∀ i,f i∈A ∧ f i∉W ∧ f i∉R ∧ ∀ v∈R,¬F.Adj (f i) v := by
  have hsingle : ∀ v∈({x}:Finset V),∀ w∈({x}:Finset V),¬F.Adj v w := by
    intro v hv w hw
    rw [Finset.mem_singleton.mp hv,Finset.mem_singleton.mp hw]
    exact F.loopless.irrefl x
  obtain ⟨u',hu'B,hxu'⟩ := common_hub_from_count H {x} B cH
    (hhub {x} (by simp;omega) hsingle) hB
  have hxu : H x u' := hxu' x (Finset.mem_singleton_self _)
  have hd1 : 0≤d+1 := by linarith
  obtain ⟨a,haA,haW,haR,_hxa,_hxa',haF⟩ := sparse_common_neighbour_avoiding Q F
    (A.filter (fun a => H a u ∧ H a u')) W R x x d c hd hF (hcount u u' x x)
    (by nlinarith only [hbudget,hd1,(show (0:ℝ)≤r from Nat.cast_nonneg _)])
  have ha : a∈A ∧ H a u ∧ H a u' := Finset.mem_filter.mp haA
  let R' := insert a R
  have hR' : (R'.card:ℝ)≤R.card+1 := by exact_mod_cast Finset.card_insert_le a R
  let A' := A.filter (fun v => H v u' ∧ H v u')
  obtain ⟨f,hf0,hf,hind,havoid⟩ := sparse_rooted_cycle_embedding Q F A' W R' a
    (Finset.mem_insert_self _ _) r hr d c hd hF (hcount u' u')
    (by nlinarith only [hbudget,hR',hd1])
  have hloc : ∀ i,f i∈A ∧ f i∉W ∧ f i∉R ∧ (∀ v∈R,¬F.Adj (f i) v) ∧ H (f i) u' := by
    intro i
    by_cases hi : i=⟨0,by omega⟩
    · subst i
      rw [hf0]
      exact ⟨ha.1,haW,haR,haF,ha.2.2⟩
    · have hh := havoid i hi
      have hmem := Finset.mem_filter.mp hh.1
      exact ⟨hmem.1,hh.2.1,(fun h => hh.2.2.1 (Finset.mem_insert_of_mem h)),
        (fun v hv => hh.2.2.2 v (Finset.mem_insert_of_mem hv)),hmem.2.1⟩
  refine ⟨f,u',hf,(fun i => (hloc i).2.2.2.2),hu'B,hxu,?_,hind,?_⟩
  · rw [hf0]
    exact ha.2.1
  · intro i
    exact ⟨(hloc i).1,(hloc i).2.1,(hloc i).2.2.1,(hloc i).2.2.2.1⟩

end Oberwolfach
