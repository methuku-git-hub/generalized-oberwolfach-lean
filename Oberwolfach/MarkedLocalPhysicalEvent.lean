module

public import Oberwolfach.MarkedLocalPhysicalCycles
public import Oberwolfach.MarkedLocalPhysicalPaths
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! One physical-edge exposure for all local marked cycles and all
common paths, with roots anywhere in the ambient vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedLocalCycleCoefficient (r : ℕ) (α θ pstar : ℝ) : ℝ :=
  pstar^(r+5)*(α*θ/4)^(r+5)/2

def markedLocalPathCoefficient (r : ℕ) (α θ pstar : ℝ) : ℝ :=
  pstar^(r+7)*(α*θ/4)^(r+4)/2

def markedLocalSurvivalExponent (r : ℕ) (α θ pstar K : ℝ) : ℝ :=
  min (2*(markedLocalCycleCoefficient r α θ pstar/K^(r+5))^2/(2*((r:ℝ)+5)^2))
    (2*(markedLocalPathCoefficient r α θ pstar/K^(r+4))^2/(2*((r:ℝ)+4)*((r:ℝ)+7)))

theorem markedLocalSurvivalExponent_pos (r : ℕ) (α θ pstar K : ℝ)
    (hα : 0<α) (hθ : 0<θ) (hpstar : 0<pstar) (hK : 0<K) :
    0<markedLocalSurvivalExponent r α θ pstar K := by
  unfold markedLocalSurvivalExponent markedLocalCycleCoefficient markedLocalPathCoefficient
  positivity

variable {V U : Type} [Fintype V] [LinearOrder V] [Fintype U]

def MarkedLocalPhysicalCounts (r b : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V)
    (T₀ TK : U→Finset V) (a : ℕ) (βC βP : ℝ) (σ : Sym2 V→Option (Bool×Bool)) : Prop :=
  (∀ u : U,βC*(a:ℝ)^(r+5)≤
    (Fintype.card {C : DenseMarkedBaseFamily P π b (r+4) (T₀ u) (TK u) //
      MarkedBaseRims P π b (r+4) σ C.val}:ℝ)) ∧
  (∀ (u : U) (j : Bool) (v v' : V),v≠v' → βP*(a:ℝ)^(r+4)≤
    (Fintype.card {C : DenseRootMarkedPathFamily P π b (r+3) j (T₀ u) (TK u) v v' //
      MarkedPathRims P π b (r+3) j v v' σ C.val}:ℝ))

theorem markedLocal_physical_event
    (r b : ℕ) (hb : 1≤b) (hr : 1≤r) (α θ pstar K : ℝ)
    (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) (hpstar : 0<pstar) (hK : 0<K) :
    ∃ N : ℕ,∀ (V U : Type) [Fintype V] [LinearOrder V] [Fintype U],
    ∀ a : ℕ,N≤a → a≤Fintype.card V → (Fintype.card V:ℝ)≤K*a → (Fintype.card U:ℝ)≤K*a →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : U→Finset V),
      (∀ u,θ*a≤((T₀ u).card:ℝ)) → (∀ u,θ*a≤((TK u).card:ℝ)) →
      (∀ u x,(1/2+α/2)*(T₀ u).card≤((P.neighborFinset x∩T₀ u).card:ℝ)) →
      (∀ u x,(1/2+α/2)*(TK u).card≤((P.neighborFinset x∩TK u).card:ℝ)) →
      (∀ u x,(1/2+α/2)*(TK u).card≤((P.neighborFinset x∩(TK u).image π).card:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),pstar≤p → pstar≤k →
    1-(2*K+4*K^3)*(a:ℝ)^3*Real.exp (-markedLocalSurvivalExponent r α θ pstar K*a)≤
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
        (MarkedLocalPhysicalCounts r b P π T₀ TK a
          (markedLocalCycleCoefficient r α θ pstar) (markedLocalPathCoefficient r α θ pstar)) := by
  obtain ⟨NC,hNC⟩ := markedBase_local_exponential_event (r+4) b hb (by omega) α θ pstar K hα hα1 hθ hpstar hK
  obtain ⟨NP,hNP⟩ := markedPath_local_exponential_event r b hb hr α θ pstar K hα hα1 hθ hpstar hK
  refine ⟨max 1 (max NC NP),?_⟩
  intro V U _ _ _ a haN han hnK huK P π T₀ TK hs₀ hsK hd₀ hdK hdπ p k hp hk hsum hpmin hkmin
  have ha : 0<a := by omega
  have haR : (1:ℝ)≤a := by exact_mod_cast ha
  let βC := markedLocalCycleCoefficient r α θ pstar
  let βP := markedLocalPathCoefficient r α θ pstar
  let cC := 2*(βC/K^(r+5))^2/(2*((r:ℝ)+5)^2)
  let cP := 2*(βP/K^(r+4))^2/(2*((r:ℝ)+4)*((r:ℝ)+7))
  let E := Real.exp (-markedLocalSurvivalExponent r α θ pstar K*a)
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let GoodC := fun σ=>∀ u : U,βC*(a:ℝ)^(r+5)≤
    (Fintype.card {C : DenseMarkedBaseFamily P π b (r+4) (T₀ u) (TK u) //MarkedBaseRims P π b (r+4) σ C.val}:ℝ)
  let J := Bool×U×{vv : V×V // vv.1≠vv.2}
  let GoodP := fun σ=>∀ z : J,βP*(a:ℝ)^(r+4)≤
    (Fintype.card {C : DenseRootMarkedPathFamily P π b (r+3) z.1 (T₀ z.2.1) (TK z.2.1) z.2.2.val.1 z.2.2.val.2 //
      MarkedPathRims P π b (r+3) z.1 z.2.2.val.1 z.2.2.val.2 σ C.val}:ℝ)
  have hC : 1-Fintype.card U*(2*Real.exp (-cC*a))≤μ.probability GoodC := by
    have hh := hNC V U a (by omega) han hnK P π T₀ TK hs₀ hsK hd₀ hdK p k hp hk hsum hpmin hkmin
    simpa only [cC,βC,markedLocalCycleCoefficient,GoodC,μ,Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_ofNat,
      show (4:ℝ)+1=5 by norm_num,add_assoc] using hh
  have hP : 1-Fintype.card J*(2*Real.exp (-cP*a))≤μ.probability GoodP := by
    exact hNP V J a (by omega) han hnK P π (fun z=>T₀ z.2.1) (fun z=>TK z.2.1)
      (fun z=>z.1) (fun z=>z.2.2.val.1) (fun z=>z.2.2.val.2) (fun z=>z.2.2.property)
      (fun z=>hs₀ z.2.1) (fun z=>hsK z.2.1) (fun z=>hd₀ z.2.1) (fun z=>hdπ z.2.1) p k hp hk hsum hpmin hkmin
  have hJ : (Fintype.card J:ℝ)≤2*K^3*(a:ℝ)^3 := by
    have hsub : Fintype.card {vv : V×V // vv.1≠vv.2}≤Fintype.card V*Fintype.card V := by
      simpa only [Fintype.card_prod] using Fintype.card_subtype_le (fun vv : V×V=>vv.1≠vv.2)
    have hsR : (Fintype.card {vv : V×V // vv.1≠vv.2}:ℝ)≤(K*a)*(K*a) := by
      have hh : (Fintype.card {vv : V×V // vv.1≠vv.2}:ℝ)≤(Fintype.card V:ℝ)*(Fintype.card V:ℝ) := by exact_mod_cast hsub
      exact hh.trans (by gcongr)
    simp only [J,Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
    calc
      2*((Fintype.card U:ℝ)*Fintype.card {vv : V×V // vv.1≠vv.2})≤2*((K*a)*((K*a)*(K*a))) := by gcongr
      _ = _ := by ring
  have heC : Real.exp (-cC*a)≤E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left cC cP)) (Nat.cast_nonneg a)
  have heP : Real.exp (-cP*a)≤E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right cC cP)) (Nat.cast_nonneg a)
  have ha3 : (a:ℝ)≤(a:ℝ)^3 := by nlinarith [sq_nonneg ((a:ℝ)-1),mul_nonneg (sub_nonneg.mpr haR) (sq_nonneg (a:ℝ))]
  have hfailC : Fintype.card U*(2*Real.exp (-cC*a))≤2*K*(a:ℝ)^3*E := by
    calc
      (Fintype.card U:ℝ)*(2*Real.exp (-cC*a))≤(K*a)*(2*E) := by gcongr
      _ ≤ (K*(a:ℝ)^3)*(2*E) := by gcongr
      _ = _ := by ring
  have hfailP : Fintype.card J*(2*Real.exp (-cP*a))≤4*K^3*(a:ℝ)^3*E := by
    calc
      (Fintype.card J:ℝ)*(2*Real.exp (-cP*a))≤(2*K^3*(a:ℝ)^3)*(2*E) := by gcongr
      _ = _ := by ring
  have hj := finiteLaw_good_intersection μ GoodC GoodP (Fintype.card J*(2*Real.exp (-cP*a))) hP
  have hjoint := (sub_le_sub_right hC (Fintype.card J*(2*Real.exp (-cP*a)))).trans hj
  have hbound : 1-(2*K+4*K^3)*(a:ℝ)^3*E≤1-Fintype.card U*(2*Real.exp (-cC*a))-Fintype.card J*(2*Real.exp (-cP*a)) := by
    nlinarith only [hfailC,hfailP]
  apply (hbound.trans hjoint).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨hσ.1,fun u j v v' hv=>hσ.2 (j,u,⟨(v,v'),hv⟩)⟩

end Oberwolfach
