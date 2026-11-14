module

public import Oberwolfach.OrdinaryRestrictedLevelTests
public import Oberwolfach.FiniteLawManyGoodEvents

@[expose] public section
/-! All fixed level-specific row and hub tests occur on the same ambient
sample, with the sum of their local-domain failure probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
  [LinearOrder V] [DecidableEq U] [DecidableEq I]

theorem ordinary_restricted_levels_common_event
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (X:I→Finset V) (Z:I→Finset U) (ρ:∀i,Equiv.Perm ↥(X i))
    (hcomm:∀i (v:↥(X i)),(ρ i v).val=π v.val)
    (hnoshort:∀i x k,0<k→k<2*d+1→((ρ i)^k) x≠x)
    (hF:∀i,permutationConflictGraph (ρ i) (3*d)≤F.induce ((X i):Set V))
    (A:∀i,Finset ↥(X i)) (B:∀i,Finset ↥(Z i))
    (hA:∀i,(A i).Nonempty) (hB:∀i,0<(B i).card)
    (j:Color) (pH:ℝ) (hj:∀u,s u j=pH) (tR tH:I→ℝ)
    (htR:∀i,0<tR i) (htH:∀i,0<tH i):
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    let Good:=fun (i:I) (raw:RawWheelOutcome V U Γ Color)=>
      RawOrdinaryRows (P.induce ((X i):Set V)) (ρ i) d 3 (A i) p (fun u=>s u.val) j (tR i)
        (ordinaryRawRestrictPair (Subtype.val:↥(X i)→V) (Subtype.val:↥(Z i)→U) raw) ∧
      RawOrdinaryDomainIndices (F.induce ((X i):Set V)) (ρ i) d 3 (B i) pH j (tH i)
        (ordinaryRawRestrictPair (Subtype.val:↥(X i)→V) (Subtype.val:↥(Z i)→U) raw);
    let failure:=fun i=>ordinaryLevelRowFailure (Fintype.card ↥(X i)) (Fintype.card ↥(Z i)) d (A i).card (tR i)+
      ordinaryLevelColumnFailure (Fintype.card ↥(X i)) d (B i).card (tH i);
    1-∑i,failure i≤μ.probability (fun raw=>∀i,Good i raw):=by
  intro μ Good failure
  have hlevel:∀i∈(Finset.univ:Finset I),1-failure i≤μ.probability (Good i):=by
    intro i _
    let φ:↥(X i)↪V:=⟨Subtype.val,Subtype.val_injective⟩
    let ψ:↥(Z i)↪U:=⟨Subtype.val,Subtype.val_injective⟩
    have hh:=ordinary_restricted_level_tests_probability φ ψ P F (ρ i) d hd p hp hp1 q hq hQ s hs hS
      (hnoshort i) (hF i) (A i) (B i) (hA i) (hB i) j pH (tR i) (tH i) hj (htR i) (htH i)
    have ht:1-ordinaryLevelRowFailure (Fintype.card ↥(X i)) (Fintype.card ↥(Z i)) d (A i).card (tR i)-
      ordinaryLevelColumnFailure (Fintype.card ↥(X i)) d (B i).card (tH i)≤μ.probability (Good i):=by
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    dsimp only [failure]
    linarith only [ht]
  have hh:=finiteLaw_many_good_events_lower μ (Finset.univ:Finset I) Good failure hlevel
  simpa only [Finset.mem_univ,true_implies] using hh
end Oberwolfach
