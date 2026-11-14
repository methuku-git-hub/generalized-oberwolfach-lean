module

public import Oberwolfach.UniformColourRound
public import Oberwolfach.HypergraphListRestriction
public import Oberwolfach.ColourIterationScales
public import Oberwolfach.PartialListColouring

@[expose] public section

/-! Finite iteration of the checked random colouring round. This theorem
constructs a proper colouring; no edge-colouring theorem is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem near_optimal_hypergraph_list_colouring
    (k : ℕ) (hk : 0<k) (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1)
    (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ D₀ : ℕ, ∀ D B : ℕ, D₀≤D → (B : ℝ)≤(D : ℝ)^(1-δ) →
      ∀ (V E C : Type) [Fintype V] [Fintype E] [Fintype C], Fintype.card C≤2*D →
      ∀ (R : E → Finset V) (L : E → Finset C) (l : ℕ),
      (∀ e,(R e).card=k) → (∀ e,(L e).card=l) →
      (∀ v,(hypergraphVertexClique R v).card≤D) →
      (∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B) →
      (1+ε)*(D : ℝ)≤l → l≤2*D →
      ∃ f : E → C,(∀ e,f e∈L e) ∧ ∀ e g,(hypergraphLineGraph R).Adj e g → f e≠f g := by
  classical
  obtain ⟨q,c,hq,hq1,hc,hround⟩ := uniform_improving_colour_round k hk ε hε hε1
  let J := ⌈(16*(k : ℝ))/c⌉₊
  have hJ : (16*(k : ℝ))≤(J : ℝ)*c := by
    have hh := Nat.le_ceil ((16*(k : ℝ))/c)
    exact (div_le_iff₀ hc).mp hh
  let a := q^J
  have ha : 0<a := pow_pos hq _
  let K := 1+(a^(1-δ))⁻¹+5*(k : ℝ)/(a^2)
  have hK : 1≤K := by
    have hh : 0≤(a^(1-δ))⁻¹ := by positivity
    have hh' : 0≤5*(k : ℝ)/(a^2) := by positivity
    dsimp [K];linarith
  obtain ⟨N,hstep⟩ := hround K δ hK hδ hδ1
  refine ⟨max 1 ⌈(N : ℝ)/a⌉₊,?_⟩
  intro D B hD hB
  have hDpos : 0<D := lt_of_lt_of_le (by omega : 0<1) ((le_max_left _ _).trans hD)
  have hDR : (0 : ℝ)<D := Nat.cast_pos.mpr hDpos
  have hND : (N : ℝ)≤a*D := by
    have hh : (N : ℝ)/a≤D := (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hD))
    have hh' := (div_le_iff₀ ha).mp hh
    linarith
  have hrec : ∀ t i : ℕ, i+t=J →
      ∀ (V E C : Type) [Fintype V] [Fintype E] [Fintype C], Fintype.card C≤2*D →
      ∀ (R : E → Finset V) (L : E → Finset C) (l s : ℕ),
      (∀ e,(R e).card=k) → (∀ e,(L e).card=l) →
      (∀ v,(hypergraphVertexClique R v).card≤D) →
      (∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B) →
      (∀ v z,(hypergraphColourClique R L v z).card≤s) →
      0<s → s≤l → l≤2*D → q^i*(D : ℝ)≤l →
      (1+ε+(i : ℝ)*c)*(s : ℝ)≤l →
      ∃ f : E → C,(∀ e,f e∈L e) ∧ ∀ e g,(hypergraphLineGraph R).Adj e g → f e≠f g := by
    intro t
    induction t with
    | zero =>
      intro i hi V E C _ _ _ hC R L l s hsize hcard hdegree hcodeg hcol hs hsl hl hlow hratio
      have hiJ : i=J := by omega
      subst i
      have hfinish : 16*(k*s)≤l := by
        have hh : (16*(k : ℝ))*(s : ℝ)≤l := by
          have hm := mul_le_mul_of_nonneg_right hJ (Nat.cast_nonneg s)
          have hc₀ : 0≤(1+ε)*(s : ℝ) := by positivity
          nlinarith
        rw [← Nat.mul_assoc]
        exact_mod_cast hh
      exact hypergraph_list_colouring_at_large_ratio R L hk hs (fun e=>(hsize e).le) hcard hcol hfinish
    | succ t ih =>
      intro i hi V E C _ _ _ hC R L l s hsize hcard hdegree hcodeg hcol hs hsl hl hlow hratio
      by_cases hfinish : 16*(k*s)≤l
      · exact hypergraph_list_colouring_at_large_ratio R L hk hs (fun e=>(hsize e).le) hcard hcol hfinish
      have hiJ : i≤J := by omega
      have hpow : q^J≤q^i := pow_le_pow_of_le_one hq.le hq1 hiJ
      have hscale : a*(D : ℝ)≤l := (mul_le_mul_of_nonneg_right hpow hDR.le).trans hlow
      have hNl : N≤l := by exact_mod_cast hND.trans hscale
      obtain ⟨_,hB',hd'⟩ := colour_iteration_scale_bounds k D l s (Fintype.card C) B hDpos hsl hl hC
        ha hδ hδ1 hscale hB
      have hr : 1+ε≤1+ε+(i : ℝ)*c := by nlinarith [mul_nonneg (Nat.cast_nonneg i) hc.le]
      have hupper : (l : ℝ)≤(16*k)*s := by
        have hh : l≤16*(k*s) := (lt_of_not_ge hfinish).le
        rw [← Nat.mul_assoc] at hh
        exact_mod_cast hh
      obtain ⟨l',s',p,L',hlpos,hspos,hll,hsl',hql,hgain,hplist,hproper,hsub,hcard',havoid,hcol'⟩ :=
        hstep l s B D hNl hs hsl hB' V E C hd' R L hsize hcard hcodeg hcol hdegree
          (1+ε+(i : ℝ)*c) hr hratio hupper
      have hlow' : q^(i+1)*(D : ℝ)≤l' := by
        calc
          _ = q*(q^i*(D : ℝ)) := by rw [pow_succ];ring
          _ ≤ q*(l : ℝ) := mul_le_mul_of_nonneg_left hlow hq.le
          _ ≤ _ := hql
      have hratio' : (1+ε+((i+1 : ℕ) : ℝ)*c)*(s' : ℝ)≤l' := by
        convert hgain using 1 <;> push_cast <;> ring
      let U := {e : E // p e=none}
      letI : Fintype U := Fintype.ofFinite U
      have hresU : ∀ v,(hypergraphVertexClique (fun e : U=>R e.val) v).card≤D := by
        intro v
        convert (hypergraph_subtype_resource_degree R (fun e=>p e=none) v).trans (hdegree v) using 1 <;>
          congr 1 <;> ext e <;> simp only [hypergraphVertexClique,Finset.mem_filter,Finset.mem_univ,true_and]
      have hcodegU : ∀ v w,v≠w →
          (Finset.univ.filter (fun e : U=>v∈R e.val ∧ w∈R e.val)).card≤B := by
        intro v w hvw
        convert (hypergraph_subtype_codegree R (fun e=>p e=none) v w).trans (hcodeg v w hvw) using 1 <;>
          congr 1 <;> ext e <;> simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hcolU : ∀ v z,(hypergraphColourClique (fun e : U=>R e.val) (fun e=>L' e.val) v z).card≤s' := by
        intro v z
        convert hcol' v z using 1 <;> congr 1 <;> ext e <;>
          simp only [hypergraphColourClique,Finset.mem_filter,Finset.mem_univ,true_and]
      obtain ⟨f,hf,hfproper⟩ := ih (i+1) (by omega) V U C hC
        (fun e=>R e.val) (fun e=>L' e.val) l' s'
        (fun e=>hsize e.val) (fun e=>hcard' e.val) hresU hcodegU hcolU
        hspos hsl' (hll.trans hl) hlow' hratio'
      exact extend_partial_list_colouring (hypergraphLineGraph R) L p hplist hproper
        (fun e=>L' e.val) (fun e=>hsub e.val)
        (fun e z hz f hef=>havoid e.val f hef z hz) f hf
        (fun e f hef=>hfproper e f ((hypergraph_subtype_adj R (fun e=>p e=none) e f).mpr hef))
  intro V E C _ _ _ hC R L l hsize hcard hdegree hcodeg hratio hl
  have hsl : D≤l := by
    have hh : (D : ℝ)≤l := by nlinarith [mul_nonneg hε.le hDR.le]
    exact_mod_cast hh
  apply hrec J 0 (by omega) V E C hC R L l D hsize hcard hdegree hcodeg ?_
    hDpos hsl hl (by simpa using (show (D : ℝ)≤l by exact_mod_cast hsl)) (by simpa using hratio)
  intro v z
  apply (Finset.card_le_card (show hypergraphColourClique R L v z⊆hypergraphVertexClique R v from ?_)).trans
    (hdegree v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2.1⟩

end Oberwolfach
