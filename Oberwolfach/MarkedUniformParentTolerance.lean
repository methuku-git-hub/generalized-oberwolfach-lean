module

public import Oberwolfach.MarkedActiveReferenceScale

@[expose] public section
/-! A single later parent tolerance can satisfy all level-record budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
namespace Oberwolfach
private theorem uniform_parent_finite_scale {I:Type} [Fintype I]
    (a b:I→ℝ) (ha:∀ i,0≤a i) (hb:∀ i,0<b i):
    ∃ k:ℝ,0<k∧∀ x:ℝ,0≤x→x≤k→∀ i,a i*x≤b i:=by
  classical
  let C:ℝ:=1+∑ i,a i/b i
  have hsum:0≤∑ i,a i/b i:=Finset.sum_nonneg (fun i _=>div_nonneg (ha i) (hb i).le)
  have hC:0<C:=by dsimp [C];linarith
  refine ⟨1/C,by positivity,?_⟩
  intro x hx hxk i
  have hi:a i/b i≤∑ j,a j/b j:=Finset.single_le_sum
    (fun j _=>div_nonneg (ha j) (hb j).le) (Finset.mem_univ i)
  have hiC:a i/b i≤C:=by dsimp [C];linarith
  have hi':a i≤C*b i:=(div_le_iff₀ (hb i)).mp hiC
  have hix:=mul_le_mul_of_nonneg_left hxk (ha i)
  apply hix.trans
  rw [mul_one_div]
  apply (div_le_iff₀ hC).mpr
  nlinarith only [hi']

theorem marked_uniform_parent_tolerance (r:ℕ)
    (κ theta x eta t cfg cut common Cp Cwide:ℝ)
    (hκ:0<κ) (htheta:0<theta) (hx:0<x) (heta:0<eta) (ht:0<t)
    (hcfg:0<cfg) (hcut:0<cut) (hcommon:0<common) (hCp:0≤Cp) (hCwide:0≤Cwide):
    ∃ δ:ℝ,0<δ ∧ δ≤1 ∧ δ≤cfg ∧ δ≤cut ∧ δ≤common ∧ δ≤κ/4 ∧
      δ+(r+12:ℕ)*δ≤κ/4 ∧ δ+(r+12:ℕ)*δ≤x/2 ∧
      δ+δ+Cp*δ≤κ/4 ∧ δ+δ+Cp*δ≤theta/4 ∧
      δ+δ+Cwide*δ≤eta/4 ∧ δ+δ≤t/8 := by
  let a:Fin 11→ℝ:=![1,1,1,1,1,1+(r+12:ℕ),1+(r+12:ℕ),2+Cp,2+Cp,2+Cwide,2]
  let b:Fin 11→ℝ:=![1,cfg,cut,common,κ/4,κ/4,x/2,κ/4,theta/4,eta/4,t/8]
  have ha:∀ i,0≤a i:=by intro i;fin_cases i <;> dsimp [a] <;> positivity
  have hb:∀ i,0<b i:=by intro i;fin_cases i <;> dsimp [b] <;> positivity
  obtain ⟨k,hk,hall⟩:=uniform_parent_finite_scale a b ha hb
  have hh:=hall k hk.le le_rfl
  have h0:=hh 0;have h1:=hh 1;have h2:=hh 2;have h3:=hh 3;have h4:=hh 4
  have h5:=hh 5;have h6:=hh 6;have h7:=hh 7;have h8:=hh 8;have h9:=hh 9;have h10:=hh 10
  norm_num [a,b] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  refine ⟨k,hk,by linarith,by linarith,by linarith,by linarith,by linarith,?_,?_,?_,?_,?_,?_⟩ <;> (try simp only [Nat.cast_add,Nat.cast_ofNat]) <;> nlinarith

/-- A common smaller error preserves both configuration inequalities and the cut gap. -/
theorem marked_uniform_parent_tolerance_with_slack (r:ℕ)
    (κ theta x eta t cfg cut common Cp Cwide βA cyc path tstar hIcut:ℝ)
    (hκ:0<κ) (htheta:0<theta) (hx:0<x) (heta:0<eta) (ht:0<t)
    (hcfg:0<cfg) (hcut:0<cut) (hcommon:0<common) (hCp:0≤Cp) (hCwide:0≤Cwide)
    (hcyc:3*βA≤cyc-(r+5:ℕ)*cfg) (hpath:3*βA≤path-(r+4:ℕ)*cfg)
    (hcutGap:2*hIcut≤tstar/8-cut):
    ∃ δ:ℝ,0<δ ∧ δ≤1 ∧ δ≤cfg ∧ δ≤cut ∧ δ≤common ∧ δ≤κ/4 ∧
      δ+(r+12:ℕ)*δ≤κ/4 ∧ δ+(r+12:ℕ)*δ≤x/2 ∧
      δ+δ+Cp*δ≤κ/4 ∧ δ+δ+Cp*δ≤theta/4 ∧
      δ+δ+Cwide*δ≤eta/4 ∧ δ+δ≤t/8 ∧
      3*βA≤cyc-(r+5:ℕ)*δ ∧ 3*βA≤path-(r+4:ℕ)*δ ∧
      2*hIcut≤tstar/8-δ := by
  obtain ⟨δ,hδ,hδ1,hδcfg,hδcut,hδcommon,hδκ,hκref,hxref,hκpot,hθpot,hload,hrow⟩:=
    marked_uniform_parent_tolerance r κ theta x eta t cfg cut common Cp Cwide
      hκ htheta hx heta ht hcfg hcut hcommon hCp hCwide
  have ha:0≤((r+5:ℕ):ℝ):=by positivity
  have hb:0≤((r+4:ℕ):ℝ):=by positivity
  have hmulA:=mul_le_mul_of_nonneg_left hδcfg ha
  have hmulB:=mul_le_mul_of_nonneg_left hδcfg hb
  refine ⟨δ,hδ,hδ1,hδcfg,hδcut,hδcommon,hδκ,hκref,hxref,hκpot,hθpot,hload,hrow,?_,?_,?_⟩ <;> linarith
end Oberwolfach
