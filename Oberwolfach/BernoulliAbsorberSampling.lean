module

public import Oberwolfach.BernoulliVertexSampling
public import Oberwolfach.AbsorberProfileSampling

@[expose] public section

/-! Bernoulli counts of the actual labelled absorbers. The free labels
alone are sampled; roots remain fixed even when absent from the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T:Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Fintype T] [DecidableEq T] {c:ℕ}

theorem labelled_absorber_free_card (R:C→Finset V) (S:VertexAbsorberTemplate c)
    (X:Finset V) (D:LabelledCycleRecord R S.val X):
    (labelledAbsorberFree R S X D).card=c*c:=by
  unfold labelledAbsorberFree
  rw [Finset.card_image_of_injective _ (fun a b h=>Sum.inl_injective (D.1.property.1 h))]
  simp only [Finset.card_univ,Fintype.card_fin]

theorem bernoulli_absorber_mean (R:C→Finset V) (S:T→VertexAbsorberTemplate c)
    (X:Finset V) (p:ℝ) (hp:0≤p) (hp1:p≤1):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>absorberGroundCount R S X (bernoulliVertexSet σ))=
      p^(c*c)*Fintype.card (LabelledAbsorberFamily R S X):=by
  exact bernoulli_support_count_mean
    (fun D:LabelledAbsorberFamily R S X=>labelledAbsorberFree R (S D.1) X D.2)
    (c*c) (fun D=>labelled_absorber_free_card R (S D.1) X D.2) p hp hp1

theorem bernoulli_absorber_tail (R:C→Finset V) (S:T→VertexAbsorberTemplate c)
    (X:Finset V) (J:ℕ) (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (v t:ℝ) (hv:0<v) (ht:0<t)
    (hvar:(Fintype.card V:ℝ)*
      (((c*c)*Fintype.card T*X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1):ℕ):ℝ)^2≤v):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>t≤|absorberGroundCount R S X (bernoulliVertexSet σ)-
        p^(c*c)*Fintype.card (LabelledAbsorberFamily R S X)|)≤2*Real.exp (-2*t^2/v):=by
  apply bernoulli_support_count_tail
    (fun D:LabelledAbsorberFamily R S X=>labelledAbsorberFree R (S D.1) X D.2)
    (c*c) ((c*c)*Fintype.card T*X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1))
    (fun D=>labelled_absorber_free_card R (S D.1) X D.2) _ p hp hp1 v t hv ht hvar
  intro x
  have hh:=labelled_absorber_local_free_vertex_count R S X Finset.univ J hJ x
  simpa only [Finset.subset_univ,true_and,Finset.card_univ] using hh

/-- The polynomial degree in the count cancels from the tail exponent. -/
theorem bernoulli_count_tail_scale (n A ε:ℝ) (hn:0<n) (hA:0<A) (h:ℕ) (hh:1≤h):
    -2*(ε*n^h)^2/(n*(A*n^(h-1))^2)= -2*ε^2/(A^2/n):=by
  have he:n^h=n^(h-1)*n:=by rw [←pow_succ];congr 1;omega
  rw [he]
  field_simp
  <;> ring

theorem bernoulli_absorber_scaled_tail (R:C→Finset V) (S:T→VertexAbsorberTemplate c)
    (hc:1≤c) (X:Finset V) (hX:X.card=c) (J:ℕ)
    (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (hn:0<Fintype.card V) (p:ℝ) (hp:0≤p) (hp1:p≤1) (ε:ℝ) (hε:0<ε):
    let D:ℝ:=((c*c)*Fintype.card T*c^c*J^(2*c+1):ℕ)+1
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>ε*(Fintype.card V:ℝ)^(c*c)≤
        |absorberGroundCount R S X (bernoulliVertexSet σ)-
          p^(c*c)*Fintype.card (LabelledAbsorberFamily R S X)|)≤
      2*Real.exp (-2*ε^2/(D^2/Fintype.card V)):=by
  let n:ℝ:=Fintype.card V
  let D:ℝ:=((c*c)*Fintype.card T*c^c*J^(2*c+1):ℕ)+1
  have hnR:0<n:=Nat.cast_pos.mpr hn
  have hD:0<D:=by dsimp [D];positivity
  have hh:=bernoulli_absorber_tail R S X J hJ p hp hp1
    (n*(D*n^(c*c-1))^2) (ε*n^(c*c)) (by positivity) (by positivity) (by
      rw [hX]
      have hd:(((c*c)*Fintype.card T*c^c*Fintype.card V^(c*c-1)*J^(2*c+1):ℕ):ℝ)≤D*n^(c*c-1):=by
        dsimp [D,n]
        push_cast
        nlinarith only [pow_nonneg (Nat.cast_nonneg (Fintype.card V): (0:ℝ)≤_) (c*c-1)]
      exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (by positivity) (by positivity) |>.mpr hd) hnR.le)
  rw [bernoulli_count_tail_scale n D ε hnR hD (c*c) (by nlinarith)] at hh
  exact hh

theorem bernoulli_root_scaled_tail (R:C→Finset V) (c J:ℕ) (hc:2≤c)
    (hR:∀ i,(R i).card=c) (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (w:C→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ i,0≤w i ∧ w i≤B/(Fintype.card V:ℝ)^(c-1))
    (hn:0<Fintype.card V) (root:V)
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (ε:ℝ) (hε:0<ε):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>ε≤|resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) root-
        p^(c-1)*hypergraphWeightedDegree R w root|)≤
      2*Real.exp (-2*ε^2/(((J:ℝ)*B+1)^2/Fintype.card V)):=by
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn
  apply bernoulli_root_load_tail R c J hc hR hJ w
    (B/(Fintype.card V:ℝ)^(c-1)) (by positivity) hw root p hp hp1 _ ε (by positivity) hε
  have he:(Fintype.card V:ℝ)^(c-1)=(Fintype.card V:ℝ)^(c-2)*Fintype.card V:=by
    rw [←pow_succ];congr 1;omega
  have heq:(Fintype.card V:ℝ)*((J:ℝ)*(Fintype.card V:ℝ)^(c-2)*
        (B/(Fintype.card V:ℝ)^(c-1)))^2=((J:ℝ)*B)^2/Fintype.card V:=by
    rw [he]
    field_simp
    <;> ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ hnR.le
  nlinarith only [mul_nonneg (Nat.cast_nonneg J) hB]

end Oberwolfach
