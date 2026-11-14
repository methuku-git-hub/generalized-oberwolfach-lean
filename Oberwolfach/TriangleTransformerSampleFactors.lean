module

public import Oberwolfach.TriangleTransformerSample
public import Oberwolfach.TriangleTransformerFactors

@[expose] public section

/-! The complete sampled two-factor step of the triangular transformer.
The factors are returned as actual subgraphs of the original graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_sample_factors (z : ℕ) (hz : 3∣z) (β ρ : ℝ)
    (hβ : 0<β) (hβ1 : β≤1) (hρ : 0<ρ) :
    ∃ s₀ : ℕ,∀ s : ℕ,s₀≤s → 3∣s → ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],
      N≤Fintype.card V → ∀ (G : SimpleGraph V) (A Z : Finset V),Z.card=z →
      ρ*Fintype.card V≤(A.card:ℝ) →
      (∀ v∈A∪Z,(3/4+β/2)*(A.card:ℝ)≤((G.neighborFinset v∩A).card:ℝ)) →
      ∃ S : Finset V,S.card=s ∧ S⊆A ∧ Disjoint S Z ∧
      ∃ M₁ M₂ : Finset (OrdinaryCycle G 3),
        (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₁.biUnion (ordinaryCycleVertices G 3)=S∪Z ∧
        (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
        (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S) := by
  obtain ⟨K,hK⟩:=triangle_transformer_sample z β ρ hβ hβ1 hρ
  obtain ⟨L,hL⟩:=two_triangle_factors_at_hub (β/2) (by positivity) z
  refine ⟨max K L,?_⟩
  intro s hs hdiv
  obtain ⟨N,hN⟩:=hK s ((le_max_left K L).trans hs)
  refine ⟨N,?_⟩
  intro V _ _ hn G A Z hZ hA hdeg
  obtain ⟨S,hScard,hSA,hSZ,hSdeg⟩:=hN V hn G A Z hZ hA hdeg
  let T:=S∪Z
  let W:Type:=(T:Set V)
  let Q:=G.induce (T:Set V)
  let S' : Finset W:=Finset.univ.filter (fun v=>v.val∈S)
  let f : W↪V:=Function.Embedding.subtype _
  have himage : S'.image f=S := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v,Finset.mem_union_left _ hv⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hS' : S'.card=s := by
    rw [←Finset.card_image_of_injective S' f.injective,himage,hScard]
  have hW : Fintype.card W=s+z := by
    have hc : Fintype.card W=T.card := by
      convert Fintype.card_coe T using 1 <;> congr!
    rw [hc]
    simp only [T,Finset.card_union_of_disjoint hSZ,hScard,hZ]
  have hQdeg (v : W) : (Q.neighborFinset v∩S').card=(G.neighborFinset v.val∩S).card := by
    apply Finset.card_bij (fun w _=>w.val)
    · intro w hw
      have hh:=Finset.mem_inter.mp hw
      have hq : Q.Adj v w := by simpa using hh.1
      have hq' : G.Adj v.val w.val:=hq
      exact Finset.mem_inter.mpr ⟨by simpa using hq',(Finset.mem_filter.mp hh.2).2⟩
    · intro w _ u _ h;exact Subtype.ext h
    · intro w hw
      have hh:=Finset.mem_inter.mp hw
      let u : W:=⟨w,Finset.mem_union_left _ hh.2⟩
      refine ⟨u,Finset.mem_inter.mpr ⟨?_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.2⟩⟩,rfl⟩
      have hg : G.Adj v.val w := by simpa using hh.1
      have hq : Q.Adj v u:=hg
      simpa using hq
  obtain ⟨M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hcross,hold⟩:=hL W Q S'
    (by rw [hS'];exact (le_max_right K L).trans hs) (by rwa [hS'])
    (by rw [hW];exact Nat.dvd_add hdiv hz) (by rw [hW,hS'];omega)
    (by intro v;rw [hS',hQdeg];convert hSdeg v.val v.property using 1 <;> ring)
  have hQ : Q.map f≤G := by
    intro v w h
    rw [SimpleGraph.map_adj] at h
    obtain ⟨a,b,hab,rfl,rfl⟩:=h
    exact hab
  let lift:=ordinaryCycleLift f hQ (r:=3)
  have hfirst:=ordinary_cycle_family_lift f hQ M₁ hpack₁
  have hsecond:=ordinary_cycle_family_lift f hQ M₂ hpack₂
  have hall : Finset.univ.image f=T := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp hv
      exact w.property
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  refine ⟨S,hScard,hSA,hSZ,M₁.image lift,M₂.image lift,hfirst.1,?_,hsecond.1,?_,?_,?_⟩
  · rw [hfirst.2,hcover₁,hall]
  · rw [hsecond.2,hcover₂,himage]
  · intro C hC D hD
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨D,hDM,rfl⟩:=Finset.mem_image.mp hD
    exact ordinaryCycleLift_disjoint_edges f hQ C D (hcross C hCM D hDM)
  · intro C hC v w h
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    change (C.val.val.map f).Adj v w at h
    rw [SimpleGraph.map_adj] at h
    obtain ⟨a,b,hab,rfl,rfl⟩:=h
    rcases hold C hCM a b hab with ha|hb
    · exact Or.inl (Finset.mem_filter.mp ha).2
    · exact Or.inr (Finset.mem_filter.mp hb).2

end Oberwolfach
