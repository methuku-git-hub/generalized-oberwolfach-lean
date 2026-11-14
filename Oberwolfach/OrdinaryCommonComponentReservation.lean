module

public import Oberwolfach.CycleComponentFrequency

@[expose] public section
/-! Choose the manuscript's common number of reserved r-cycles in each
prescribed factor, before sampling. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_common_component_reservation
    (β:ℝ) (hβ:0<β) (hβ1:β≤1) (r:ℕ) (hr:3≤r):
    ∃N:ℕ,∀n≥N,∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)),
      (∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=r)).card:ℝ))→
      let s₀:=β/100
      let k:=⌊s₀*(n:ℝ)/(r:ℝ)⌋₊
      let s:ℝ:=(r:ℝ)*(k:ℝ)/(n:ℝ);
      s₀/2≤s ∧ s≤s₀ ∧
      ∃C:∀w,Finset (F w).ConnectedComponent,
        (∀w,(C w).card=k) ∧ (∀w c,c∈C w→Fintype.card c=r) :=by
  let N:=max 1 ⌈200*(r:ℝ)/β⌉₊
  refine ⟨N,?_⟩
  intro n hn U _ F hfreq s₀ k s
  have hn0:0<n:=by dsimp [N] at hn;omega
  have hnR:0<(n:ℝ):=by exact_mod_cast hn0
  have hrR:0<(r:ℝ):=by exact_mod_cast (show 0<r by omega)
  have hnlarge:(200*(r:ℝ))/β≤n:=by
    have hh:⌈200*(r:ℝ)/β⌉₊≤n:=by dsimp [N] at hn;omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast hh)
  have hnumerator:2*(r:ℝ)≤s₀*n:=by
    have hh:200*(r:ℝ)≤β*n:=by
      have hh' := (div_le_iff₀ hβ).1 hnlarge
      nlinarith
    dsimp [s₀]
    linarith
  have hx:2≤s₀*n/(r:ℝ):=(le_div_iff₀ hrR).2 (by linarith)
  have hx0:0≤s₀*n/(r:ℝ):=by linarith
  have hkUpper:(k:ℝ)≤s₀*n/r:=by dsimp [k];exact Nat.floor_le hx0
  have hkLower:s₀*n/r<(k:ℝ)+1:=by dsimp [k];exact Nat.lt_floor_add_one _
  have hFracLow:s₀/2≤s:=by
    dsimp [s]
    apply (le_div_iff₀ hnR).2
    have hh:(s₀*n/r)≤2*(k:ℝ):=by linarith
    have ht:=mul_le_mul_of_nonneg_right hh hrR.le
    have heq:(s₀*n/r)*(r:ℝ)=s₀*n:=by field_simp
    rw [heq] at ht
    nlinarith
  have hFracHigh:s≤s₀:=by
    dsimp [s]
    apply (div_le_iff₀ hnR).2
    have ht:=mul_le_mul_of_nonneg_right hkUpper hrR.le
    have heq:(s₀*n/r)*(r:ℝ)=s₀*n:=by field_simp
    rw [heq] at ht
    nlinarith
  refine ⟨hFracLow,hFracHigh,?_⟩
  have hEach:∀w:U,∃C:Finset (F w).ConnectedComponent,C.card=k ∧ ∀c∈C,Fintype.card c=r:=by
    intro w
    let T:Finset (F w).ConnectedComponent:=Finset.univ.filter (fun c=>Fintype.card c=r)
    have hcount:((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=r)).card:ℝ)=r*(T.card:ℝ):=by
      have hh:=component_size_vertex_count (F w) r
      dsimp only at hh
      exact_mod_cast hh
    have hβn:β*(n:ℝ)≤(r:ℝ)*T.card:=by linarith [hfreq w]
    have hs0:s₀≤β:=by dsimp [s₀];linarith
    have hcap:s₀*n/(r:ℝ)≤T.card:=by
      apply (div_le_iff₀ hrR).2
      have hh:=mul_le_mul_of_nonneg_right hs0 (Nat.cast_nonneg n)
      nlinarith
    have hkcap:k≤T.card:=by exact_mod_cast (hkUpper.trans hcap)
    obtain ⟨C,hsub,hcard⟩:=Finset.exists_subset_card_eq hkcap
    refine ⟨C,hcard,?_⟩
    intro c hc
    exact (Finset.mem_filter.mp (hsub hc)).2
  choose C hcard hC using hEach
  exact ⟨C,hcard,hC⟩
end Oberwolfach
