module

public import Oberwolfach.HypergraphColorSampling

@[expose] public section

/-! Independent edge colours preserve every fixed nonnegative weight sum.
This is the edge-partition step, before any proper edge colouring is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {E C J : Type*} [Fintype E] [Fintype C] [Fintype J]
    [DecidableEq E] [Nonempty C]

theorem singleton_hypergraphWeightedDegree (w : E → ℝ) (e : E) :
    hypergraphWeightedDegree (fun f : E=>{f}) w e=w e := by
  unfold hypergraphWeightedDegree
  simp only [Finset.mem_singleton]
  simp

theorem singleton_monochromaticWeightedSum (w : E → ℝ) (c : C) (σ : E → C) :
    monochromaticWeightedSum (fun e : E=>{e}) w c σ=∑ e,if σ e=c then w e else 0 := by
  unfold monochromaticWeightedSum
  apply Finset.sum_congr rfl
  intro e _
  rw [patternValue_indicator]
  simp only [Finset.mem_singleton,forall_eq]
  split_ifs <;> simp

theorem weightedEdgeColoring_tail (w : E → ℝ) (hw : ∀ e,0≤w e)
    (hW : 0<∑ e,w e) (b : ℝ) (hb : ∀ e,w e≤b) (c : C) (t : ℝ) (ht : 0≤t) :
    (FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)).probability
      (fun σ=>t≤|(∑ e,if σ e=c then w e else 0)-(∑ e,w e)/Fintype.card C|)≤
      2*Real.exp (-2*t^2/(b*∑ e,w e)) := by
  have hh := monochromaticWeightedSum_tail (fun e : E=>{e}) w hw 1 (by omega)
    (fun _=>Finset.card_singleton _) hW b (by intro e;rw [singleton_hypergraphWeightedDegree];exact hb e) c t ht
  simpa only [singleton_monochromaticWeightedSum,pow_one,Nat.cast_one,mul_one] using hh

theorem weightedEdgeColoring_exists (w : J → E → ℝ) (hw : ∀ j e,0≤w j e)
    (hW : ∀ j,0<∑ e,w j e) (b : J → ℝ) (hb : ∀ j e,w j e≤b j)
    (t : J → ℝ) (ht : ∀ j,0≤t j)
    (hsmall : (∑ j : J,∑ _c : C,2*Real.exp (-2*(t j)^2/(b j*∑ e,w j e)))<1) :
    ∃ σ : E → C,∀ j c,|(∑ e,if σ e=c then w j e else 0)-(∑ e,w j e)/Fintype.card C|<t j := by
  let μ := FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)
  let A : J×C → (E → C) → Prop := fun jc σ=>
    t jc.1≤|(∑ e,if σ e=jc.2 then w jc.1 e else 0)-(∑ e,w jc.1 e)/Fintype.card C|
  let p : J×C → ℝ := fun jc=>2*Real.exp (-2*(t jc.1)^2/(b jc.1*∑ e,w jc.1 e))
  have hp : (∑ jc,p jc)<1 := by simpa only [p,Fintype.sum_prod_type] using hsmall
  obtain ⟨σ,_hσ,hgood⟩ := finiteLaw_common_event_exists μ Finset.univ A p
    (by intro jc _;exact weightedEdgeColoring_tail (w jc.1) (hw jc.1) (hW jc.1) (b jc.1) (hb jc.1) jc.2 (t jc.1) (ht jc.1)) hp
  exact ⟨σ,fun j c=>lt_of_not_ge (hgood (j,c) (Finset.mem_univ _))⟩

end Oberwolfach
