module

public import Oberwolfach.ThinnedCommonClassEvent
public import Oberwolfach.ThinnedMarkedExposure
public import Oberwolfach.MarkedBaseUniformEvent
public import Oberwolfach.MarkedPathUniformEvent
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! Common cycles and root-omitted paths with the original thinning coins.
The first exposure proves density of the actual classes; the second uses
one categorical physical-edge sample for every root and both path types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def CommonClassDensity (P : SimpleGraph V) (π : Equiv.Perm V) (α astar : ℝ) (T : Bool→Finset V) : Prop :=
  Disjoint (T false) (T true) ∧ Disjoint (T false) ((T true).image π) ∧
  ∀ b,(astar/2*Fintype.card V≤((T b).card:ℝ)) ∧
    (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩T b).card:ℝ)) ∧
    (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩(T b).image π).card:ℝ))

def CommonClassConfigurationCounts (P : SimpleGraph V) (π : Equiv.Perm V) (d r : ℕ)
    (α astar pstar : ℝ) (T : Bool→Finset V) (τ : Sym2 V→Option (Bool×Bool)) : Prop :=
  ((pstar^(r+5)*(α*(astar/2)/4)^(r+5)/2)*(Fintype.card V:ℝ)^(r+5)≤
    (Fintype.card {C : DenseMarkedBaseFamily P π (3*d) (r+4) (T false) (T true) //
      MarkedBaseRims P π (3*d) (r+4) τ C.val}:ℝ)) ∧
  (∀ v v' : V,v≠v' → ∀ j : Bool,
    (pstar^(r+7)*(α*(astar/2)/4)^(r+4)/2)*(Fintype.card V:ℝ)^(r+4)≤
      (Fintype.card {C : DenseRootMarkedPathFamily P π (3*d) (r+3) j (T false) (T true) v v' //
        MarkedPathRims P π (3*d) (r+3) j v v' τ C.val}:ℝ))

theorem thinnedCommon_configurations_event
    (r : ℕ) (hr : 1≤r) (α astar pstar : ℝ)
    (hα : 0<α) (hα1 : α≤1/2) (hastar : 0<astar) (hpstar : 0<pstar)
    (d Q : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1),pstar≤p → pstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U),u≠u' →
      astar≤q u g*q u' g → astar≤s u j*s u' j*θ →
    1-1/(Fintype.card V:ℝ)^Q≤
      (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability
        (fun σ=>CommonClassDensity P π α astar (thinnedCommonClass π d g j u u' σ) ∧
          CommonClassConfigurationCounts P π d r α astar pstar
            (thinnedCommonClass π d g j u u' σ) (thinnedMarkedPhysicalPart σ)) := by
  obtain ⟨N₁,hN₁pos,hN₁⟩ := thinnedCommonClass_dense_event α astar hα hα1 hastar d (Q+1) hd
  obtain ⟨N₂,hN₂⟩ := markedBase_uniform_event (r+4) (3*d) (by omega) (by omega)
    α (astar/2) pstar hα (by linarith) (by positivity) hpstar 0 (Q+1)
  obtain ⟨N₃,hN₃⟩ := markedPath_uniform_event r (3*d) (by omega) hr
    α (astar/2) pstar hα (by linarith) (by positivity) hpstar 2 (Q+1)
  refine ⟨max 3 (max N₁ (max N₂ N₃)),by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN P π hP hnoshort p k hp hk hphys hpmin hkmin q hq hQ s hs hS θ hθ hθ1 g j u u' hu hqmin hsmin
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let μ := thinnedMarkedPairLaw (V:=V) d hd q hq hQ s hs hS θ hθ hθ1
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hphys)
  let T := fun ρ : ThinnedMarkedPairOutcome V U Γ Color=>
    thinnedCommonClass π d g j u u' (thinnedMarkedJoin ρ (fun _=>none))
  let E := fun ρ : ThinnedMarkedPairOutcome V U Γ Color=>CommonClassDensity P π α astar (T ρ)
  let A := fun (ρ : ThinnedMarkedPairOutcome V U Γ Color) τ=>CommonClassConfigurationCounts P π d r α astar pstar (T ρ) τ
  have hfirst : 1-1/(n:ℝ)^(Q+1)≤μ.probability E := by
    have hh := hN₁ V U Γ Color (by omega) P π hP hnoshort p k hp hk hphys q hq hQ s hs hS θ hθ hθ1 g j u u' hu hqmin hsmin
    change 1-1/(n:ℝ)^(Q+1)≤
      (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability
        (fun σ=>E (thinnedMarkedPairPart σ)) at hh
    rw [thinnedMarked_first_probability] at hh
    exact hh
  have hsecond (ρ : ThinnedMarkedPairOutcome V U Γ Color) (hρ : E ρ) :
      1-2/(n:ℝ)^(Q+1)≤ν.probability (A ρ) := by
    have hbase := hN₂ V Unit (by omega) (by simp) P π
      (fun _=>T ρ false) (fun _=>T ρ true)
      (fun _=>(hρ.2.2 false).1) (fun _=>(hρ.2.2 true).1)
      (fun _=>(hρ.2.2 false).2.1) (fun _=>(hρ.2.2 true).2.1)
      p k hp hk hphys hpmin hkmin
    let J := Bool×{a : V×V // a.1≠a.2}
    have hJ : Fintype.card J≤2*n^2 := by
      have hsub := Fintype.card_subtype_le (fun a : V×V=>a.1≠a.2)
      simp only [Fintype.card_prod] at hsub
      change Fintype.card (Bool×{a : V×V // a.1≠a.2})≤_
      simp only [Fintype.card_prod,Fintype.card_bool]
      exact Nat.mul_le_mul_left 2 (by simpa only [pow_two] using hsub)
    have hpaths := hN₃ V J (by omega) hJ P π
      (fun _=>T ρ false) (fun _=>T ρ true) (fun a=>a.1) (fun a=>a.2.val.1) (fun a=>a.2.val.2)
      (fun a=>a.2.property) (fun _=>(hρ.2.2 false).1) (fun _=>(hρ.2.2 true).1)
      (fun _=>(hρ.2.2 false).2.1) (fun _=>(hρ.2.2 true).2.2)
      p k hp hk hphys hpmin hkmin
    have hjoint := finiteLaw_good_intersection ν
      (fun τ=>∀ _ : Unit,
        (pstar^(r+4+1)*(α*(astar/2)/4)^(r+4+1)/2)*(Fintype.card V:ℝ)^(r+4+1)≤
          (Fintype.card {C : DenseMarkedBaseFamily P π (3*d) (r+4) (T ρ false) (T ρ true) //
            MarkedBaseRims P π (3*d) (r+4) τ C.val}:ℝ)) _ (1/(n:ℝ)^(Q+1)) hpaths
    have hb := (sub_le_sub_right hbase (1/(n:ℝ)^(Q+1))).trans hjoint
    have heq : 1-2/(n:ℝ)^(Q+1)=1-1/(n:ℝ)^(Q+1)-1/(n:ℝ)^(Q+1) := by ring
    rw [heq]
    apply hb.trans
    apply finiteLaw_probability_mono
    intro τ hτ
    refine ⟨?_,fun v v' hv j=>hτ.2 (j,⟨(v,v'),hv⟩)⟩
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hτ.1 ()
  have hjoint := finiteLaw_product_good_lower μ ν E A (1/(n:ℝ)^(Q+1)) (2/(n:ℝ)^(Q+1))
    (by positivity) hfirst hsecond
  have hsum := scaled_inverse_power_le n Q hn 3 (by exact_mod_cast (show 3≤n by dsimp [n];omega))
  have hb : 1-1/(n:ℝ)^Q≤1-1/(n:ℝ)^(Q+1)-2/(n:ℝ)^(Q+1) := by
    convert sub_le_sub_left hsum 1 using 1 <;> ring
  rw [thinnedMarked_two_exposures]
  exact hb.trans hjoint

end Oberwolfach
