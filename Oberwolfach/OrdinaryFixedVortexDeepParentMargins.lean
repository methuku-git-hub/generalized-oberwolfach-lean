module

public import Oberwolfach.OrdinaryDeepParentMarginsFromNumeric
public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry
public import Oberwolfach.OrdinaryFixedVortexConflictDegree
public import Oberwolfach.OrdinaryVortexLevelParentDensityBalance
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! Discharge the triangle fresh-parent numerical margins from the original
fixed-vortex geometry, up to the explicitly chosen small-parameter hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_deep_parent_margins
    (β ε ρ₀ α pmin Kdom ηHub εf γ κ δparent εparent tpot lam b Bweight:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hε:0<ε) (hε1:ε<1/4)
    (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)
    (num:OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηHub εf (2*Kdom)
      γ κ δparent εparent tpot lam b Bweight)
    (hβbalance:β≤2*δparent*(ρ₀/8)*pmin) (d:ℕ):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (θhost pR pH εR εH Ledit:ℝ),cycleThreshold 3≤θhost→
      (θhost+α)*Fintype.card V≤D→pmin≤pR→pR≤1→pmin≤pH→pH≤1→
      pR=initialIndexDensity U D*pH→0≤εR→2*εR≤εparent→0≤εH→2*εH≤εparent→0≤Ledit→
    ∀i,i<Q.length→
    let f:=markedVortexVertexEmbedding Q i;let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    Ledit≤lam*I.card→
    OrdinaryDeepParentMargins (P.comap f) ((permutationConflictGraph π (3*d)).comap f) I B
      γ κ b Bweight εf ηHub (ρ₀/8) pmin pR pH (θhost+α-β/2) (εR*I.card) (εH*B.card)
      (2*((3*d:ℕ):ℝ)) Ledit δparent εparent tpot (2*Kdom) (pR*β*I.card):=by
  have hK1:1≤Kdom:=by
    have hh:1≤1+1/(ε/2)+1/((ε/2)*(ρ₀/8)):=by
      have h1:0≤1/(ε/2):=by positivity
      have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
      linarith
    exact hh.trans hKdom
  have hK:0<Kdom:=lt_of_lt_of_le zero_lt_one hK1
  let Lconf:ℝ:=2*((3*d:ℕ):ℝ)
  have hL:0≤Lconf:=by dsimp [Lconf];positivity
  obtain ⟨N,hN⟩:=exists_nat_ge (Lconf/lam)
  let M:=max N 1
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  obtain ⟨v₁,hv₁,hgeom⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨max v₀ v₁,by omega,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ θhost pR pH εR εH Ledit
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hLedit i hi f I B hEdit
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hpR0:0≤pR:=hpmin.le.trans hpR
  have hpH0:0≤pH:=hpmin.le.trans hpH
  have hδparent:0<δparent:=num.delta_pos
  have hs:=hsize V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi
  have hg:=hgeom V U P D vsize hreg hn hD hρlo hρhi (by omega) Q i hi
  have hI:M≤I.card:=hg.2.2.1
  have hIpos:0<I.card:=by dsimp [M] at hI;omega
  have hIr:(0:ℝ)<I.card:=by exact_mod_cast hIpos
  have hW:(Fintype.card (markedVortexVertexType Q i):ℝ)≤Kdom*I.card:=by
    have hh:=hs.2.2.2.1
    exact hh.trans (mul_le_mul_of_nonneg_right hKdom hIr.le)
  have hUW:Fintype.card (markedVortexHubType Q i)≤Fintype.card (markedVortexVertexType Q i):=by
    exact (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε (by omega) i hi).2.2
  have hphysical:(Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ)≤(2*Kdom)*I.card:=by
    simp only [Fintype.card_sum,Nat.cast_add]
    have hu:(Fintype.card (markedVortexHubType Q i):ℝ)≤Fintype.card (markedVortexVertexType Q i):=by exact_mod_cast hUW
    nlinarith only [hW,hu]
  have hAfrac:(1/Kdom)*(Fintype.card (markedVortexVertexType Q i):ℝ)≤I.card:=by
    have hh:(Fintype.card (markedVortexVertexType Q i):ℝ)/Kdom≤I.card:=
      (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hW)
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh
  have hLsmall:Lconf≤lam*I.card:=by
    have hNI:(N:ℝ)≤I.card:=by exact_mod_cast (show N≤I.card by dsimp [M] at hI;omega)
    have hh:(Lconf/lam)≤(I.card:ℝ):=hN.trans hNI
    simpa only [mul_comm] using (div_le_iff₀ num.lambda_pos).mp hh
  have hF:∀v,(((permutationConflictGraph π (3*d)).comap f).degree v:ℝ)≤Lconf:=by
    intro v
    have hh:=ordinary_fixed_vortex_conflict_degree P D vsize β ε Q π hπ i (3*d) v
    have hh':(((permutationConflictGraph π (3*d)).comap f).degree v:ℝ)≤(2*(3*d):ℕ):=by exact_mod_cast hh
    simpa only [Lconf,Nat.cast_mul,Nat.cast_ofNat] using hh'
  have hfields:=ordinary_vortex_level_parent_density_balance P D vsize β ε θhost α (initialIndexDensity U D) pH
    Q hn hreg rfl hρ hβ hpH0 hdegree i (by omega)
  have hparent:∀v,|pR*(I∩(P.comap f).neighborFinset v).card-2*pH*B.card|≤pR*β*I.card:=by
    intro v
    have hh:=hfields.2 v
    rw [←hpEq] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hbalance:pR*β*I.card≤δparent*(2*B.card*pH):=by
    have hcoef:pR*β≤2*δparent*(ρ₀/8)*pH:=by
      have h1:pR*β≤β:=by nlinarith only [hpR1,hβ]
      have h2:2*δparent*(ρ₀/8)*pmin≤2*δparent*(ρ₀/8)*pH:=by gcongr
      linarith only [h1,hβbalance,h2]
    have h1:=mul_le_mul_of_nonneg_right hcoef hIr.le
    have h2:=mul_le_mul_of_nonneg_left hg.2.2.2.2.1 (show 0≤2*δparent*pH by positivity)
    nlinarith only [h1,h2]
  have hthreshold:cycleThreshold 3≤θhost+α-β/2:=by linarith
  have hrow:εR*I.card≤εparent*I.card/2:=by
    have hh:=mul_le_mul_of_nonneg_right hεRsmall hIr.le
    nlinarith only [hh]
  have hcolumn:εH*B.card≤εparent*B.card/2:=by
    have hh:=mul_le_mul_of_nonneg_right hεHsmall (show (0:ℝ)≤B.card by positivity)
    nlinarith only [hh]
  have hout:=ordinary_deep_parent_margins_from_numeric (P.comap f) ((permutationConflictGraph π (3*d)).comap f) I B
    γ κ b Bweight εf ηHub (ρ₀/8) pmin pR pH (θhost+α-β/2) (εR*I.card) (εH*B.card)
    Lconf Ledit δparent εparent tpot (2*Kdom) (pR*β*I.card) (1/Kdom) lam num hpmin (by positivity) (by positivity)
    hIpos hAfrac hphysical hg.2.2.2.2.1 hg.2.2.2.2.2.1 hpR hpR1 hpH hpH1 hL hLsmall hLedit hEdit hF
    hparent hbalance hthreshold hfields.1 hrow hcolumn
  convert hout using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach
