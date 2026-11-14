module

public import Oberwolfach.ColourRoundErrorMargins
public import Oberwolfach.ColourRoundIntegerParameters
public import Oberwolfach.PaddedColourRound

@[expose] public section

/-! A full round with integer parameters, exact shortened lists, and
uniform ratio progress. All new constants precede the hypergraph. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_improving_colour_round (k : ℕ) (hk : 0<k)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ q c : ℝ, 0<q ∧ q≤1 ∧ 0<c ∧
      ∀ K δ : ℝ, 1≤K → 0<δ → δ≤1 →
      ∃ N : ℕ, ∀ l s B D : ℕ, N≤l → 0<s → s≤l →
      (B : ℝ)≤K*(l : ℝ)^(1-δ) →
      ∀ (V E C : Type) [Fintype V] [Fintype E] [Fintype C],
      ((k*(D+Fintype.card C*s) : ℕ) : ℝ)≤K*(l : ℝ)^2 →
      ∀ (R : E → Finset V) (L : E → Finset C),
      (∀ e, (R e).card=k) → (∀ e, (L e).card=l) →
      (∀ v w, v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B) →
      (∀ v a, (hypergraphColourClique R L v a).card≤s) →
      (∀ v, (hypergraphVertexClique R v).card≤D) →
      ∀ r : ℝ, 1+ε≤r → r*s≤l → (l : ℝ)≤(16*k)*s →
      ∃ l' s' : ℕ, ∃ (p : E → Option C) (L' : E → Finset C),
        0<l' ∧ 0<s' ∧ l'≤l ∧ s'≤l' ∧ q*l≤l' ∧ (r+c)*s'≤l' ∧
        (∀ e a, p e=some a → a∈L e) ∧
        (∀ e f, (hypergraphLineGraph R).Adj e f → ∀ a, p e=some a → p f≠some a) ∧
        (∀ e, L' e⊆L e) ∧ (∀ e, (L' e).card=l') ∧
        (∀ e f, (hypergraphLineGraph R).Adj e f → ∀ a, a∈L' e → p f≠some a) ∧
        (∀ v a, (hypergraphColourClique (fun e : {e // p e=none}=>R e.val)
          (fun e=>L' e.val) v a).card≤s') := by
  let a := Real.exp (-2*(k : ℝ))
  let M : ℝ := 16*k
  let b := 1-Real.exp (-1/M)
  have hkR : (0 : ℝ)<k := Nat.cast_pos.mpr hk
  have hM : 0<M := by dsimp [M];positivity
  have ha : 0<a := Real.exp_pos _
  have ha1 : a≤1 := by
    dsimp [a]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hb : 0<b := by
    have hh : Real.exp (-1/M)<1 := Real.exp_lt_one_iff.mpr (by
      exact div_neg_of_neg_of_pos (by norm_num) hM)
    dsimp [b];linarith
  have hb1 : b≤1 := by dsimp [b];linarith [Real.exp_pos (-1/M)]
  let c := a*ε/4
  let q := b^k/2
  let η := min (b^k/4) (c*b^(k-1)/(2*M*(M+2)))
  have hc : 0<c := by dsimp [c];positivity
  have hq : 0<q := by dsimp [q];positivity
  have hq1 : q≤1 := by
    have hh := pow_le_one₀ hb.le hb1 (n := k)
    dsimp [q];linarith
  have hη : 0<η := by
    dsimp [η]
    apply lt_min <;> positivity
  have hηsmall : η≤b^k/2 := (min_le_left _ _).trans (by nlinarith [pow_pos hb k])
  have herror : η*M*(M+2)≤c*b^(k-1) := by
    have hh := (le_div_iff₀ (show 0<2*M*(M+2) by positivity)).mp (min_le_right _ _ : η≤_)
    nlinarith [mul_pos hc (pow_pos hb (k-1))]
  refine ⟨q,c,hq,hq1,hc,?_⟩
  intro K δ hK hδ hδ1
  let τ := η/(24*((k : ℝ)+1))
  have hτ : 0<τ := by dsimp [τ];positivity
  obtain ⟨N₀,hN₀⟩ := colouring_round_eventually_valid k hk K δ τ hK hδ hδ1 hτ
  obtain ⟨N₁,hN₁⟩ := colouring_round_errors_eventually_small k K δ η (by linarith) hδ hη
  refine ⟨max N₀ N₁,?_⟩
  intro l s B D hn hs hsl hB V E C _ _ _ hd R L hsize hcard hcodeg hdegree hresource r hr hratio hlarge
  obtain ⟨hl,hcodegsmall,htail,hprob⟩ := hN₀ l ((le_max_left _ _).trans hn) s B _ hs hsl hB hd
  obtain ⟨_,hηl,herrL,herrS⟩ := hN₁ l ((le_max_right _ _).trans hn) s B hsl hB
  have hlpos : (0 : ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hsR : (0 : ℝ)<s := Nat.cast_pos.mpr hs
  let ρ := (1-1/(l : ℝ))^(k*s)
  let κ := 1-(s : ℝ)*ρ/(l : ℝ)
  have hρbounds := equalized_retention_rate_bounds (by omega : 0<l) (k*s)
  have hκbounds := colouring_available_rate_bounds (by omega : 0<l) hsl hρbounds
  have harho : a≤ρ := colouring_retention_lower_bound hl hsl
  have hrM : r≤M := by dsimp [M];nlinarith
  have hbκ : b≤κ := by
    have hpow := colouring_retention_upper_bound (k := k) (s := s) hl
    have hratio' : 1/M≤((k*s : ℕ) : ℝ)/(l : ℝ) := by
      apply (div_le_div_iff₀ hM hlpos).mpr
      have hk1 : (1 : ℝ)≤k := by exact_mod_cast hk
      change (l : ℝ)≤(16*k)*s at hlarge
      dsimp [M];push_cast
      nlinarith [mul_nonneg (show 0≤(k : ℝ)-1 by linarith) (show (0 : ℝ)≤(16*(k : ℝ))*s by positivity)]
    have he : Real.exp (-((k*s : ℕ) : ℝ)/(l : ℝ))≤Real.exp (-1/M) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hratio'
    have hρup : ρ≤Real.exp (-1/M) := hpow.trans he
    dsimp [b,κ]
    linarith [hκbounds.1]
  have hcodegNat : 2*(k^2*(k^2*B))≤l := by
    have he : (2 : ℝ)*(((k^2*(k^2*B) : ℕ) : ℝ))=2*(k : ℝ)^4*B := by push_cast;ring
    rw [← he] at hcodegsmall
    exact_mod_cast hcodegsmall
  obtain ⟨p,L₀,hp,hproper,hsub,havoid,hlist,hrem⟩ := padded_colour_round R L hk hl hs hsl
    hsize hcard hcodeg hdegree hresource hcodegNat (mul_pos hτ hlpos)
    (by simpa only [neg_div,mul_assoc] using htail)
    (by simpa only [neg_div] using hprob)
  obtain ⟨l',s',hl',hs',hll,hsl',hfloor,hceil,hql,hgain⟩ := colouring_round_integer_parameters hk
    (by omega : 0<l) hs ha ha1 hb hε hε1 hη ⟨harho,hρbounds.2⟩ hr hrM
    hratio hlarge hbκ hκbounds.2 herror hηsmall hηl
  have havail (e : E) : l'≤(L₀ e).card := by
    have hh := hlist e
    have hreal : (l' : ℝ)≤(L₀ e).card := by linarith
    exact_mod_cast hreal
  choose L' hsub' hcard' using fun e => Finset.exists_subset_card_eq (havail e)
  refine ⟨l',s',p,L',hl',hs',hll,hsl',hql,hgain,hp,hproper,
    fun e=>(hsub' e).trans (hsub e),hcard',?_,?_⟩
  · intro e f hef z hz
    exact havoid e f hef z (hsub' e hz)
  · intro v z
    have hsubcl : hypergraphColourClique (fun e : {e // p e=none}=>R e.val)
        (fun e=>L' e.val) v z ⊆ hypergraphColourClique (fun e : {e // p e=none}=>R e.val)
        (fun e=>L₀ e.val) v z := by
      intro e he
      obtain ⟨_,hv,hz⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,hsub' e.val hz⟩
    have hc₀ := hrem v z
    have hc₁ : ((hypergraphColourClique (fun e : {e // p e=none}=>R e.val)
        (fun e=>L₀ e.val) v z).card : ℝ)≤s' := by linarith
    exact (Finset.card_le_card hsubcl).trans (by exact_mod_cast hc₁)

end Oberwolfach
