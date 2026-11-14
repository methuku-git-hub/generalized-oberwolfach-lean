module

public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.RawOrdinaryDomainIndexEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The level-specific row and hub tests have their natural local-domain
failure bounds on the original ambient raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

def ordinaryLevelRowFailure (n u:ℕ) (d:ℕ) (vcount:ℕ) (t:ℝ):ℝ:=
  (n+1:ℝ)^3*(u+1:ℝ)^3*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*(2*(3:ℝ)+1)*vcount))))

def ordinaryLevelColumnFailure (n:ℕ) (d:ℕ) (ucount:ℕ) (t:ℝ):ℝ:=
  (n+1:ℝ)^3*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((3+1:ℝ)*ucount))))

theorem ordinary_restricted_level_tests_probability
    (φ:W↪V) (ψ:Z↪U) (P F:SimpleGraph V) (ρ:Equiv.Perm W) (d:ℕ) (hd:2≤d)
    (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x k,0<k→k<2*d+1→(ρ^k) x≠x)
    (hF:permutationConflictGraph ρ (3*d)≤F.comap φ)
    (A:Finset W) (B:Finset Z) (hA:A.Nonempty) (hB:0<B.card)
    (j:Color) (pH tR tH:ℝ) (hj:∀u,s u j=pH) (htR:0<tR) (htH:0<tH):
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    let Row:=fun raw:RawWheelOutcome V U Γ Color=>RawOrdinaryRows (P.comap φ) ρ d 3 A p
      (fun u=>s (ψ u)) j tR (ordinaryRawRestrictPair φ ψ raw);
    let Col:=fun raw:RawWheelOutcome V U Γ Color=>RawOrdinaryDomainIndices (F.comap φ) ρ d 3 B pH j tH
      (ordinaryRawRestrictPair φ ψ raw);
    1-ordinaryLevelRowFailure (Fintype.card W) (Fintype.card Z) d A.card tR-
      ordinaryLevelColumnFailure (Fintype.card W) d B.card tH≤μ.probability (fun raw=>Row raw ∧ Col raw):=by
  intro μ Row Col
  let q':Z→Γ→ℝ:=fun z=>q (ψ z)
  let s':Z→Color→ℝ:=fun z=>s (ψ z)
  let μlocal:=FiniteLaw.pi (rawWheelLaw (V:=W) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd
    q' (fun z=>hq (ψ z)) (fun z=>hQ (ψ z)) s' (fun z=>hs (ψ z)) (fun z=>hS (ψ z)))
  let RowLocal:RawWheelOutcome W Z Γ Color→Prop:=RawOrdinaryRows (P.comap φ) ρ d 3 A p s' j tR
  let ColLocal:RawWheelOutcome W Z Γ Color→Prop:=RawOrdinaryDomainIndices (F.comap φ) ρ d 3 B pH j tH
  have hr:=rawOrdinaryRows_common_event (P.comap φ) ρ d hd p hp hp1 q' (fun z=>hq (ψ z))
    (fun z=>hQ (ψ z)) s' (fun z=>hs (ψ z)) (fun z=>hS (ψ z)) hnoshort A hA 3 j tR htR
  have hc:=rawOrdinaryDomainIndices_common_event (F.comap φ) ρ (fun _=>p) (fun _=>hp) (fun _=>hp1)
    d hd q' (fun z=>hq (ψ z)) (fun z=>hQ (ψ z)) s' (fun z=>hs (ψ z)) (fun z=>hS (ψ z))
    hnoshort hF B hB 3 j pH (fun z=>hj (ψ z)) tH htH
  have hprojR:=ordinary_raw_pair_restriction_probability φ φ.injective ψ ψ.injective p hp hp1 d hd q hq hQ s hs hS RowLocal
  have hprojC:=ordinary_raw_pair_restriction_probability φ φ.injective ψ ψ.injective p hp hp1 d hd q hq hQ s hs hS ColLocal
  have hr':1-ordinaryLevelRowFailure (Fintype.card W) (Fintype.card Z) d A.card tR≤μ.probability Row:=by
    rw [hprojR]
    dsimp only [ordinaryLevelRowFailure]
    convert hr using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hc':1-ordinaryLevelColumnFailure (Fintype.card W) d B.card tH≤μ.probability Col:=by
    rw [hprojC]
    dsimp only [ordinaryLevelColumnFailure]
    convert hc using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact finiteLaw_intersection_lower μ Row Col _ _ hr' hc'
end Oberwolfach
