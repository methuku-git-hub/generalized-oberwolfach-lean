module

public import Oberwolfach.OrdinaryUniformRows
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.PermutationEmbeddingWindows
public import Oberwolfach.VortexUniformEvents

@[expose] public section
/-! All bounded row tests on fixed shrinking levels hold on one ambient
sample with a uniform terminal-size threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_rows_vortex_event
    (h d:ℕ) (hd:2≤d) (ε K η χ:ℝ) (hε:0<ε) (hK:1≤K)
    (hη:0<η) (hη1:η<1) (hχ:0<χ):
    ∃M₀:ℕ,1≤M₀ ∧ ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(P:SimpleGraph V) (π:Equiv.Perm V),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(f:∀i,W i↪V) (g:∀i,Z i↪U) (ρ:∀i,Equiv.Perm (W i)),
      (∀i x,f i (ρ i x)=π (f i x))→
    ∀(A:∀i,Finset (W i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
      (∀i≤L,(Fintype.card (W i):ℝ)≤K*(A i).card)→
      (∀i≤L,(Fintype.card (Z i):ℝ)≤K*(A i).card)→
    ∀(p:ℝ) (hp:0≤p) (hp1:p≤1)
      (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑a,q u a)) (j:Color),
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀i≤L,RawOrdinaryRows (P.comap (f i)) (ρ i) d h (A i) p
        (fun z=>s (g i z)) j (ε*(A i).card) (ordinaryRawRestrictPair (f i) (g i) σ)):=by
  let c:=ordinaryRowsExponent h d ε
  have hc:0<c:=ordinary_rows_exponent_pos h d ε hε
  obtain ⟨M₀,hM1,hM⟩:=vortex_exponential_common_event (2*ordinaryRowsCoefficient h K) c η χ (2*h) hc hη hη1 hχ
  refine ⟨M₀,hM1,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P π hnoshort f g ρ hcomm A L hn hstep hW hZ
    p hp hp1 q hq hQ s hs hS j
  let μ:FiniteLaw (RawWheelOutcome V U Γ Color):=
    FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)
  let Good:=fun i (σ:RawWheelOutcome V U Γ Color)=>
    RawOrdinaryRows (P.comap (f i)) (ρ i) d h (A i) p (fun z=>s (g i z)) j (ε*(A i).card)
      (ordinaryRawRestrictPair (f i) (g i) σ)
  apply hM (RawWheelOutcome V U Γ Color) μ (fun i=>(A i).card) L hn hstep Good
  intro i hi
  let Local:=fun σ:RawWheelOutcome (W i) (Z i) Γ Color=>
    RawOrdinaryRows (P.comap (f i)) (ρ i) d h (A i) p (fun z=>s (g i z)) j (ε*(A i).card) σ
  have hlaw:=ordinary_raw_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
    p hp hp1 d hd q hq hQ s hs hS Local
  change _≤μ.probability (fun σ=>Local (ordinaryRawRestrictPair (f i) (g i) σ))
  rw [hlaw]
  apply raw_ordinary_rows_exponential_event (P.comap (f i)) (ρ i) d hd p hp hp1
    (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
    (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) _
    (A i) (Finset.card_pos.mp (lt_of_lt_of_le (by omega:0<M₀) (hn i hi))) K ε hK hε (hW i hi) (hZ i hi) h j
  intro x k hk hkd he
  have hh:=congrArg (f i) he
  rw [permutation_embedding_power (f i) π (ρ i) (hcomm i) k x] at hh
  exact hnoshort (f i x) k hk hkd hh
end Oberwolfach
