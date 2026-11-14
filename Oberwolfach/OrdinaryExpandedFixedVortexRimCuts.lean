module

public import Oberwolfach.VortexMarkedParentDegrees
public import Oberwolfach.OrdinaryExpandedInducedRimPrior
public import Oberwolfach.MarkedFixedVortexEventInputs
public import Oberwolfach.VortexCommonEvents
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The original sample and one common family of orientation coins satisfy
all fixed-vortex induced rim cuts at once, together with any prior event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_fixed_vortex_rim_cuts
    (α αcut pstar β ε ρ₀ χ:ℝ)
    (hα:0<α) (hαcut:0<αcut) (hαcut1:αcut≤1/2) (hαcutα:αcut≤α/2)
    (hpstar:0<pstar) (hβ:0≤β) (hβα:β≤α/8) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχ:0<χ):
    ∃v₀:ℕ,1≤v₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize),
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),pstar≤2*p→
    ∀d:ℕ,∀hd:2≤d,
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let κ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-εE≤((μ.sigma ν).prod κ).probability E→
    1-(εE+χ)≤((μ.sigma ν).prod κ).probability (fun z=>E z∧∀i,i<Q.length→
      OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pstar):=by
  obtain ⟨N,hN⟩:=ordinary_expanded_induced_rim_cut_with_prior αcut pstar hαcut hαcut1 hpstar 1
  obtain ⟨M,hM⟩:=exists_nat_gt (1/((1-ε)*χ))
  let M₀:=max N (max M 1)
  have hM0:1≤M₀:=by dsimp [M₀];omega
  have hM0pos:(0:ℝ)<M₀:=by exact_mod_cast (show 0<M₀ by omega)
  have hMχ:1/((1-ε)*(M₀:ℝ))≤χ:=by
    have hden:0<(1-ε)*χ:=mul_pos (by linarith) hχ
    have hle:(M:ℝ)≤M₀:=by exact_mod_cast (show M≤M₀ by dsimp [M₀];omega)
    have hbig:1/((1-ε)*χ)≤(M₀:ℝ):=hM.le.trans hle
    have hh:1≤((1-ε)*χ)*(M₀:ℝ):=by simpa only [mul_comm] using (div_le_iff₀ hden).mp hbig
    apply (div_le_iff₀ (mul_pos (by linarith) hM0pos)).mpr
    nlinarith only [hh]
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M₀
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hdegree hρlo hρhi hv Q
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR d hd q hq hQ s hs hS R _ ν E εE μ κ hE
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤1/2+α by linarith) (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  let L:=Q.length-1
  let I:=fun i=>Q.extendedVertices (i+1)
  let Good:=fun (i:ℕ) (z:(Σσ,R σ)×(Sym2 V→Bool))=>
    OrdinaryInducedRimCutEvent (I i)
      (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pstar
  have hI:∀i≤L,M₀≤(I i).card:=by
    intro i hi
    have hh:=hsize V U P D vsize hreg hn hDhalf hρlo hρhi hv Q i (by have :=Q.length_pos;dsimp [L] at *;omega)
    have hcard:((markedVortexInnerVertices Q i).card:ℝ)=(I i).card:=by
      exact_mod_cast (marked_vortex_inner_cardinalities Q i).1
    have he:0≤ε*((I i).card:ℝ):=by positivity
    have hs:=hh.2.1
    rw [hcard] at hs
    exact_mod_cast (show (M₀:ℝ)≤(I i).card by nlinarith only [hs,he])
  have hstep:∀i<L,((I (i+1)).card:ℝ)≤ε*(I i).card:=by
    intro i hi
    have hh:=(Q.extended_successor_size_bounds hε.le (i+1)).1
    simpa only [I,Nat.add_assoc] using hh
  have hpos:∀i≤L,0<((I i).card:ℝ):=by
    intro i hi
    exact_mod_cast (show 0<(I i).card by have hh:=hI i hi;omega)
  have hlast:(M₀:ℝ)≤((I L).card:ℝ):=by exact_mod_cast (hI L (by omega))
  have hSingle:∀i≤L,1-1/((I i).card:ℝ)≤((μ.sigma ν).prod κ).probability (Good i):=by
    intro i hi
    have hlocal:∀v:I i,(1/2+αcut)*(I i).card≤((P.induce ((I i):Set V)).degree v:ℝ):=by
      intro v
      have hj:i+1≤Q.length:=by have :=Q.length_pos;dsimp [L] at *;omega
      have hx:v.val∈Q.vertices ((i+1)-2):=by
        have hx':v.val∈Q.extendedVertices ((i+1)-2):=Q.extendedVertices_subset (by omega) v.property
        rwa [Q.extendedVertices_eq (by omega : (i+1)-2≤Q.length)] at hx'
      have hdeg:=Q.marked_parent_degrees hreg hn hdegree hα hρ hβ hβα hβ1 hj v.val hx
      have hcoef:=mul_le_mul_of_nonneg_right (show (1/2+αcut:ℝ)≤1/2+α/2 by linarith)
        (show (0:ℝ)≤(Q.vertices (i+1)).card by positivity)
      have hIeq:I i=Q.vertices (i+1):=Q.extendedVertices_eq hj
      have hh:=hcoef.trans hdeg.2.2.1
      rw [←hIeq] at hh
      rw [induced_degree_intersection]
      exact hh
    have hnI:N≤(I i).card:=by
      have hh:=hI i hi
      dsimp [M₀] at hh
      omega
    have htrue:1-(0:ℝ)≤((μ.sigma ν).prod κ).probability (fun _=>True):=by simp [finiteLaw_probability_true]
    have hh:=hN V U Γ Color P (I i) hnI hlocal p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR d hd
      q hq hQ s hs hS ν (fun _=>True) 0 htrue
    simpa only [zero_add,sub_zero,pow_one,true_and,Good] using hh
  have hcommon:=vortex_fixed_domain_common_event ((μ.sigma ν).prod κ) ε (M₀:ℝ) hε (by linarith) hM0pos
    (fun i=>(I i).card) L hpos hstep hlast Good hSingle
  have hcommon':1-χ≤((μ.sigma ν).prod κ).probability (fun z=>∀i≤L,Good i z):=
    le_trans (by linarith only [hMχ]) hcommon
  have hboth:=finiteLaw_intersection_lower ((μ.sigma ν).prod κ) E (fun z=>∀i≤L,Good i z) εE χ hE hcommon'
  have hboth':1-(εE+χ)≤((μ.sigma ν).prod κ).probability (fun z=>E z ∧ ∀i≤L,Good i z):=by
    linarith only [hboth]
  apply hboth'.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  intro i hi
  exact hz.2 i (by have :=Q.length_pos;dsimp [L];omega)
end Oberwolfach
