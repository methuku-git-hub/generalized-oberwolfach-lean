module

public import Oberwolfach.ColourRoundRealization
public import Oberwolfach.PaddedColourRoundTransport
public import Oberwolfach.ColourRoundNumerics

@[expose] public section

/-! One complete colouring round on the original edge and colour types.
Auxiliary edges affect the experiment but are removed from its conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem padded_colour_round
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C)
    {k l B s D : ℕ} (hk : 0<k) (hl : 1<l) (hs : 0<s) (hsl : s≤l)
    (hsize : ∀ e,(R e).card=k) (hcard : ∀ e,(L e).card=l)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s)
    (hresource : ∀ v,(hypergraphVertexClique R v).card≤D)
    (hcodegsmall : 2*(k^2*(k^2*B))≤l)
    {t : ℝ} (ht : 0<t)
    (hsmall : (l : ℝ)*(4*Real.exp (-t^2/
      (12*(k : ℝ)*(l : ℝ)+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ))))≤t)
    (hprob : 8*((k : ℝ)+1)*Real.exp (-t^2/
      (12*(k : ℝ)*(l : ℝ)+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ)))≤
      1/(4*((s*(1+k*l)*(k*(D+Fintype.card C*s)+1)^4 : ℕ) : ℝ))) :
    let ρ := (1-1/(l : ℝ))^(k*s)
    let κ := 1-(s : ℝ)*ρ/(l : ℝ)
    ∃ (p : E → Option C) (L' : E → Finset C),
      (∀ e c,p e=some c → c∈L e) ∧
      (∀ e f,(hypergraphLineGraph R).Adj e f → ∀ c,p e=some c → p f≠some c) ∧
      (∀ e,L' e⊆L e) ∧
      (∀ e f,(hypergraphLineGraph R).Adj e f → ∀ c,c∈L' e → p f≠some c) ∧
      (∀ e,(l : ℝ)*κ^k-(6*((k : ℝ)+1)*t+
        (l : ℝ)*((2 : ℝ)^k*((k^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ)))≤(L' e).card) ∧
      (∀ z c,((hypergraphColourClique (fun e : {e // p e=none}=>R e.val)
        (fun e=>L' e.val) z c).card : ℝ)≤
        (s : ℝ)*(1-ρ)*κ^(k-1)+6*((k : ℝ)+1)*t+
        (s : ℝ)*(1/(l : ℝ)+ρ*(2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1)))+
          (2 : ℝ)^(k-1)*(((k-1)^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ))) := by
  classical
  dsimp only
  let Rp := paddedResources R L s
  let Lp := paddedColourList R L s l
  let H : Finset (E ⊕ ColourPaddingVertex R L s) := Finset.univ.map Function.Embedding.inl
  have hH (e) (he : e∈H) : ∃ f,e=Sum.inl f := by
    obtain ⟨f,_,hf⟩ := Finset.mem_map.mp he
    exact ⟨f,hf.symm⟩
  have hreal (e) (he : e∈H) : (Rp e).card=k := by
    obtain ⟨f,rfl⟩ := hH e he
    exact hsize f
  have heq (e) (he : e∈H) (v) (hv : v∈Rp e) (c) (hc : c∈Lp e) :
      (hypergraphColourClique Rp Lp v c).card=s := by
    obtain ⟨f,rfl⟩ := hH e he
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hc
    exact paddedColourClique_card_original R L s l hdegree v b
  obtain ⟨σ,hσ,hlist,hremain⟩ := colour_round_realization Rp Lp H hk hl hs hsl
    (paddedResources_size R L s (by omega) (fun e=>(hsize e).le)) hreal
    (paddedColourList_card R L s (by omega) hcard)
    (fun v w hvw=>by
      dsimp only [Rp]
      rw [paddedResources_codegree R L s v w hvw]
      exact hcodeg v w hvw)
    (paddedColourClique_degree_bound R L (by omega) l hdegree) heq
    (paddedLineGraph_degree_bound R L s (by omega) (fun e=>(hsize e).le) hresource)
    hcodegsmall ht hsmall hprob
  let p := paddedRetainedOriginal R L s l σ
  let L' := paddedAvailableOriginal R L s l σ
  refine ⟨p,L',paddedRetainedOriginal_list R L s l σ (fun e=>hσ (Sum.inl e)),
    fun e f hef c hc=>paddedRetainedOriginal_proper R L s l σ e f hef c hc,
    paddedAvailableOriginal_subset R L s l σ,
    fun e f hef c hc=>paddedAvailableOriginal_avoids_retained R L s l σ e f hef c hc,?_,?_⟩
  · intro e
    have hh := hlist (Sum.inl e) (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,rfl⟩)
    dsimp only [Rp,paddedResources] at hh
    rw [← paddedAvailableOriginal_card] at hh
    have hb := (abs_le.mp hh).1
    dsimp only [L']
    linarith
  · intro z c
    let U := realColourClass Rp Lp H z (Sum.inl c)
    have hUs : U.card≤s := (Finset.card_le_card (realColourClass_subset Rp Lp H z (Sum.inl c))).trans
      (paddedColourClique_degree_bound R L (by omega) l hdegree z (Sum.inl c))
    have hh := hremain z (Sum.inl c)
    dsimp only at hh
    have htrans := padded_residual_colour_degree_bound R L s l σ (fun e=>hσ (Sum.inl e)) z c
    have htR : ((hypergraphColourClique (fun e : {e // p e=none}=>R e.val)
        (fun e=>L' e.val) z c).card : ℝ)≤
        (remainingColourVertices (hypergraphLineGraph Rp) U (fun e=>(Rp e).erase z)
          (hypergraphVertexClique Rp) (Sum.inl c) σ).card := by exact_mod_cast htrans
    have hρ := equalized_retention_rate_bounds (by omega : 0<l) (k*s)
    have hκ := colouring_available_rate_bounds (by omega : 0<l) hsl hρ
    have hκ0 : 0≤1-(s : ℝ)*(1-1/(l : ℝ))^(k*s)/(l : ℝ) := by linarith [hρ.2,hκ.1]
    have hUsR : (U.card : ℝ)≤s := by exact_mod_cast hUs
    have hfactor : 0≤(1-(1-1/(l : ℝ))^(k*s))*
        (1-(s : ℝ)*(1-1/(l : ℝ))^(k*s)/(l : ℝ))^(k-1) :=
      mul_nonneg (sub_nonneg.mpr hρ.2) (pow_nonneg hκ0 _)
    have hmpos : (0 : ℝ)<(l : ℝ)-1 := by
      have hh : (1 : ℝ)<l := by exact_mod_cast hl
      linarith
    have herr : 0≤1/(l : ℝ)+(1-1/(l : ℝ))^(k*s)*
        (2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1)))+
        (2 : ℝ)^(k-1)*(((k-1)^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ) := by
      have hρ0 := hρ.1
      positivity
    have hb := (abs_le.mp hh).2
    have hc₁ := mul_le_mul_of_nonneg_right hUsR hfactor
    have hc₂ := mul_le_mul_of_nonneg_right hUsR herr
    dsimp only [U] at hUsR hc₁ hc₂
    dsimp only [U] at htR
    nlinarith

end Oberwolfach
