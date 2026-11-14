module

public import Oberwolfach.ThinnedCommonWitnessEvent
public import Oberwolfach.MarkedLoadFailureBounds
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! Explicit exponential failure bounds for the single common-weight
witness event. The coefficient function is fixed across all hub pairs,
and the exponent does not depend on the actual marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def commonWeightLoadExponent (m d : ℕ) (B ε : ℝ) : ℝ :=
  2*ε^2/((16*(d:ℝ)+14)^2*2*((m:ℝ)+1)^7*B^2)

theorem commonWeightLoadExponent_pos (m d : ℕ) (B ε : ℝ) (hB : 0<B) (hε : 0<ε) :
    0<commonWeightLoadExponent m d B ε := by unfold commonWeightLoadExponent;positivity

theorem commonWeightLoad_tail_exponential (m d : ℕ) (B ε n : ℝ) (hn : 0<n) :
    2*Real.exp (-2*ε^2/((16*(d:ℝ)+14)^2*(((m:ℝ)+1)^4*B/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B)))=
      2*Real.exp (-commonWeightLoadExponent m d B ε*n) := by
  congr 2
  unfold commonWeightLoadExponent
  field_simp <;> ring

theorem rawMarked_common_weight_exponential_event
    {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (m : ℕ) (hm : 3≤m) (g : Γ) (j : Color) (s₀ D τ A B : ℝ) (hs₀ : 0<s₀) (hB : 0<B)
    (hq₀ : ∀ u,q u g=s₀/m) (hs₀' : ∀ u,s u j=s₀)
    (weight : (Fin (m+1)→V)→ℝ)
    (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (pstar : ℝ) (hpstar : 0<pstar) (hpmin : pstar≤p) (hkmin : pstar≤k) (hsmin : pstar≤s₀*s₀/m)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀*s₀/m≤1) (ε : ℝ) (hε : 0<ε) :
    1-8*(Fintype.card V:ℝ)^4*Real.exp
      (-commonWeightLoadExponent m d (2*B/pstar^(2*m+1)) ε*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ u u',u≠u' → ∃ κ,CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight
        (τ+ε) σ (rawMarkedPairSpokes π d σ g j) κ u u') := by
  have hh := rawMarked_common_weight_witness_event P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
    m hm g j s₀ D τ A B hs₀ hB hq₀ hs₀' weight hw hn hDlo hDhi
    pstar hpstar hpmin hkmin hsmin hp1 hk1 hs1 ε hε
  dsimp only at hh
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  rw [commonWeightLoad_tail_exponential m d (2*B/pstar^(2*m+1)) ε (Fintype.card V) hnR] at hh
  have hroots := marked_root_domain_card (V:=V) (U:=Unit) (by simpa only [Fintype.card_unique] using Nat.succ_le_of_lt hn)
  have hrootsR : (Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×Unit)):ℝ)≤4*(Fintype.card V:ℝ)^2 := by exact_mod_cast hroots
  have hpairs : (Fintype.card (U×U):ℝ)≤(Fintype.card V:ℝ)^2 := by
    have hh' := Nat.mul_le_mul hu hu
    simpa only [Fintype.card_prod,Nat.cast_mul,pow_two] using (show (Fintype.card U:ℝ)*Fintype.card U≤(Fintype.card V:ℝ)*Fintype.card V by exact_mod_cast hh')
  have hprod := mul_le_mul hpairs hrootsR (Nat.cast_nonneg _) (by positivity)
  have herr := mul_le_mul_of_nonneg_right hprod
    (show 0≤2*Real.exp (-commonWeightLoadExponent m d (2*B/pstar^(2*m+1)) ε*Fintype.card V) by positivity)
  apply le_trans _ hh
  nlinarith only [herr]

end Oberwolfach
