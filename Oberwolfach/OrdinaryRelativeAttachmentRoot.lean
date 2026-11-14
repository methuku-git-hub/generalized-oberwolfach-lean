module

public import Oberwolfach.OrdinarySparseExpansionHubs
public import Oberwolfach.OrdinaryAttachmentRootEmbedding

@[expose] public section

/-! An attached wheel in the relative common-neighbour host, together
with the otherwise unused private zero label. New labels avoid the given
sets and all old-row separation neighbourhoods. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_relative_attachment_root (Q F : SimpleGraph V) (H : V → U → Prop)
    (A W R : Finset V) (B : Finset U) (x : V) (hx : x∈R) (r : ℕ) (hr : 3≤r) (d c cH : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+r+6)*(d+1)<c)
    (hhub : ∀ T:Finset V,T.card≤r → (∀ v∈T,∀ w∈T,¬F.Adj v w) →
      cH≤((common Finset.univ T (fun v => Finset.univ.filter (H v))).card:ℝ))
    (hB : (B.card:ℝ)<cH) :
    ∃ (f : Fin r ↪ V) (u : U),
      (∀ i j,i≠⟨0,by omega⟩ → j≠⟨0,by omega⟩ →
        (SimpleGraph.cycleGraph r).Adj i j → Q.Adj (f i) (f j)) ∧
      (∀ j,(SimpleGraph.cycleGraph r).Adj ⟨0,by omega⟩ j → Q.Adj x (f j)) ∧
      H x u ∧ (∀ j,j≠⟨0,by omega⟩ → H (f j) u) ∧ u∉B ∧
      (∀ i j,¬F.Adj (f i) (f j)) ∧
      ∀ j,f j∈A ∧ f j∉W ∧ f j∉R ∧ ∀ v∈R,¬F.Adj (f j) v := by
  have hd1 : 0≤d+1 := by linarith
  obtain ⟨g,hg0,hg,hind,havoid⟩ := sparse_rooted_cycle_embedding Q F A W R x hx r hr d c hd hF hcount
    (by nlinarith only [hbudget,hd1])
  let z : Fin r := ⟨0,by omega⟩
  let T := Finset.univ.image g
  have hTc : T.card≤r := Finset.card_image_le.trans (by simp)
  have hTF : ∀ v∈T,∀ w∈T,¬F.Adj v w := by
    intro v hv w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact hind i j
  obtain ⟨u,hu,hHu⟩ := common_hub_from_count H T B cH (hhub T hTc hTF) hB
  have hRT : ((R∪T).card:ℝ)≤R.card+r := by
    have hh := Finset.card_union_le R T
    exact_mod_cast hh.trans (Nat.add_le_add_left hTc R.card)
  obtain ⟨a,haA,haW,haRT,_hxa,_hxa',haF⟩ := sparse_common_neighbour_avoiding Q F A W (R∪T) x x d c hd hF
    (hcount x x) (by nlinarith only [hbudget,hRT,hd1])
  have hga : ∀ i,g i≠a := by
    intro i he
    exact haRT (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩))
  let f := replaceEmbeddingVertex g z a hga
  have hf0 : f z=a := replaceEmbeddingVertex_at g z a hga
  have hfn (i : Fin r) (hi : i≠z) : f i=g i := replaceEmbeddingVertex_ne g z a hga i hi
  refine ⟨f,u,?_,?_,?_,?_,hu,?_,?_⟩
  · intro i j hi hj hij
    rw [hfn i hi,hfn j hj]
    exact hg i j hij
  · intro j hj
    rw [hfn j hj.ne.symm,←hg0]
    exact hg z j hj
  · exact hHu _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,hg0⟩)
  · intro j hj
    rw [hfn j hj]
    exact hHu _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · intro i j
    by_cases hi : i=z <;> by_cases hj : j=z
    · rw [hi,hj,hf0];exact F.loopless.irrefl a
    · rw [hi,hf0,hfn j hj]
      exact haF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    · rw [hj,hf0,hfn i hi]
      exact fun h => haF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)) h.symm
    · rw [hfn i hi,hfn j hj];exact hind i j
  · intro j
    by_cases hj : j=z
    · rw [hj,hf0]
      exact ⟨haA,haW,(fun h => haRT (Finset.mem_union_left _ h)),
        fun v hv => haF v (Finset.mem_union_left _ hv)⟩
    · rw [hfn j hj]
      exact havoid j hj

end Oberwolfach
