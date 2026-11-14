module

public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.FiniteProductBothMaps

@[expose] public section
/-! Restrict the raw sample and independent fair orientation coins to the
same fixed injected vertex and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_raw_pair_coin_restriction_probability
    {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
    (f:W↪V) (g:Z↪U) (p:ℝ) (hp:0≤p) (hp1:p≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
    (s:U→Color→ℝ) (hs:∀u a,0≤s u a) (hS:∀u,∑a,s u a≤ intervalUncoveredProbability d (∑a,q u a))
    (E:RawWheelOutcome W Z Γ Color×(Sym2 W→Bool)→Prop):
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)
    let μlocal:=FiniteLaw.pi (rawWheelLaw (V:=W) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd
      (fun z=>q (g z)) (fun z=>hq (g z)) (fun z=>hQ (g z))
      (fun z=>s (g z)) (fun z=>hs (g z)) (fun z=>hS (g z)))
    let νlocal:=FiniteLaw.pi (fun _:Sym2 W=>FiniteLaw.fairCoin);
    (μ.prod ν).probability (fun z=>E (ordinaryRawRestrictPair f g z.1,fun e=>z.2 (Sym2.map f e)))=
      (μlocal.prod νlocal).probability E :=by
  intro μ ν μlocal νlocal
  have hraw:μ.map (ordinaryRawRestrictPair f g)=μlocal:=by
    apply finiteLaw_ext
    intro a
    have hh:=ordinary_raw_pair_restriction_probability f f.injective g g.injective p hp hp1 d hd q hq hQ s hs hS (fun x=>x=a)
    have hh':(μ.map (ordinaryRawRestrictPair f g)).probability (fun x=>x=a)=μlocal.probability (fun x=>x=a):=by
      rw [finiteLaw_map_probability]
      exact hh
    have hsingle (law:FiniteLaw (RawWheelOutcome W Z Γ Color)):
        law.probability (fun x=>x=a)=law.mass a:=by
      unfold FiniteLaw.probability
      rw [Finset.sum_eq_single a]
      · simp
      · intro x hx hne
        simp [hne]
      · intro h
        exact False.elim (h (Finset.mem_univ a))
    exact (hsingle _).symm.trans (hh'.trans (hsingle _))
  have hcoin:ν.map (fun coins e=>coins (Sym2.map f e))=νlocal:=by
    exact finiteLaw_pi_injective_projection (fun _:Sym2 V=>FiniteLaw.fairCoin) (Sym2.map f) (Sym2.map.injective f.injective)
  have hprod:=finiteLaw_prod_map_both μ ν (ordinaryRawRestrictPair f g) (fun coins e=>coins (Sym2.map f e))
  rw [hraw,hcoin] at hprod
  have he:=finiteLaw_map_probability (μ.prod ν) (fun z=>(ordinaryRawRestrictPair f g z.1,fun e=>z.2 (Sym2.map f e))) E
  rw [hprod] at he
  exact he.symm
end Oberwolfach
