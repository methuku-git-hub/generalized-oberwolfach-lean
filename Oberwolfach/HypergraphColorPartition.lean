module

public import Oberwolfach.HypergraphColorClasses

@[expose] public section

/-! One vertex-colouring event controls every root and every fixed edge
weight simultaneously. The root colour may subsequently be chosen as the
realised colour of that root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E C J : Type*} [Fintype V] [Fintype E] [Fintype C] [Fintype J]
    [DecidableEq V] [Nonempty C]

theorem hypergraphColorPartition_exists
    (R : E → Finset V) (k : ℕ) (hk : 2≤k) (hR : ∀ e,(R e).card=k)
    (hdegree : ∀ v,0<Fintype.card (HypergraphEdgesAt R v))
    (D : ℝ) (hD : 0≤D)
    (hcodegree : ∀ v u,u≠v → ((Finset.univ.filter (fun e=>v∈R e ∧ u∈R e)).card:ℝ)≤D)
    (w : J → E → ℝ) (hw : ∀ j e,0≤w j e) (hW : ∀ j,0<∑ e,w j e)
    (L : J → ℝ) (hL : ∀ j v,hypergraphWeightedDegree R (w j) v≤L j)
    (t : V → ℝ) (s : J → ℝ) (ht : ∀ v,0≤t v) (hs : ∀ j,0≤s j)
    (hsmall :
      (∑ v : V,∑ _c : C,2*Real.exp (-2*(t v)^2/(D*((k:ℝ)-1)*Fintype.card (HypergraphEdgesAt R v))))+
      (∑ j : J,∑ _c : C,2*Real.exp (-2*(s j)^2/(L j*k*∑ e,w j e)))<1) :
    ∃ σ : V → C,
      (∀ v c,|monochromaticWeightedSum (hypergraphRootRemainder R v) (fun _=>1) c σ-
        (Fintype.card (HypergraphEdgesAt R v):ℝ)/(Fintype.card C:ℝ)^(k-1)|<t v) ∧
      (∀ j c,|(∑ e∈hypergraphColorClass R σ c,w j e)-(∑ e,w j e)/(Fintype.card C:ℝ)^k|<s j) := by
  let μ := FiniteLaw.pi (fun _ : V=>FiniteLaw.uniform C)
  let A : (V×C)⊕(J×C) → (V → C) → Prop := Sum.elim
    (fun vc σ=>t vc.1≤|monochromaticWeightedSum (hypergraphRootRemainder R vc.1) (fun _=>1) vc.2 σ-
      (Fintype.card (HypergraphEdgesAt R vc.1):ℝ)/(Fintype.card C:ℝ)^(k-1)|)
    (fun jc σ=>s jc.1≤|monochromaticWeightedSum R (w jc.1) jc.2 σ-
      (∑ e,w jc.1 e)/(Fintype.card C:ℝ)^k|)
  let p : (V×C)⊕(J×C) → ℝ := Sum.elim
    (fun vc=>2*Real.exp (-2*(t vc.1)^2/(D*((k:ℝ)-1)*Fintype.card (HypergraphEdgesAt R vc.1))))
    (fun jc=>2*Real.exp (-2*(s jc.1)^2/(L jc.1*k*∑ e,w jc.1 e)))
  have hb (a : (V×C)⊕(J×C)) (_ha : a∈Finset.univ) : μ.probability (A a)≤p a := by
    cases a with
    | inl vc =>
      rcases vc with ⟨v,c⟩
      exact hypergraphRootColor_tail R k hk hR v (hdegree v) D hD (hcodegree v) c (t v) (ht v)
    | inr jc =>
      rcases jc with ⟨j,c⟩
      exact monochromaticWeightedSum_tail R (w j) (hw j) k (by omega) hR (hW j) (L j) (hL j) c (s j) (hs j)
  have hp : (∑ a,p a)<1 := by
    simpa only [Fintype.sum_sum_type,Fintype.sum_prod_type,p,Sum.elim_inl,Sum.elim_inr] using hsmall
  obtain ⟨σ,_hσ,hgood⟩ := finiteLaw_common_event_exists μ Finset.univ A p hb hp
  refine ⟨σ,?_,?_⟩
  · intro v c
    exact lt_of_not_ge (hgood (Sum.inl (v,c)) (Finset.mem_univ _))
  · intro j c
    have hh := lt_of_not_ge (hgood (Sum.inr (j,c)) (Finset.mem_univ _))
    rw [hypergraphColorClass_weight]
    exact hh

end Oberwolfach
