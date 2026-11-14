module

public import Oberwolfach.OrdinaryCombinedTriangleEvent
public import Oberwolfach.OrdinaryCombinedTriangleAtLeast

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_full_host_and_triangle_inputs_named_at_least
    (kmin d:ℕ) (hd:2≤d) (θ α pstar ω βP ηP L:ℝ)
    (hθ:cycleThreshold 3≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4)
    (hβhub:βP≤ω*pstar^9/4) (hηP:0<ηP) (hL:0≤L):
    ∃ (k:ℕ) (βH c B:ℝ),5≤k ∧ kmin≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ ∀ηH:ℝ,0<ηH→∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ P:SimpleGraph V,(∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight:OrdinaryCycle P 3→ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(3-2)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (F:SimpleGraph V) (π:Equiv.Perm V),
      (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ pR pH D₀:ℝ,∀ hRlo:pstar≤pR,∀ hRhi:pR≤1,pstar≤pH→pH≤1→
      (Fintype.card V:ℝ)/2≤D₀→
      (∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V) → pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hS)
    1-(1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2)≤
      μ.probability (ordinaryCombinedTriangleEvent d k P F π θ α pstar βP ηP ηH βH c B pR pH weight j) := by
  obtain ⟨k,βH,c,B,hk,hkmin,hβH,hc,hB,hbase⟩:=ordinary_full_host_and_triangle_inputs_at_least
    kmin d hd θ α pstar ω βP ηP L hθ hα hα1 hθ1 hpstar hpstar1 hω
    hβP hβmax hβhub hηP hL
  refine ⟨k,βH,c,B,hk,hkmin,hβH,hc,hB,?_⟩
  intro ηH hηH
  obtain ⟨ε,hε,N,hbase⟩:=hbase ηH hηH
  refine ⟨ε,hε,N,?_⟩
  intro V _ _ hn P hP
  obtain ⟨weight,hw,hedge,hbase⟩:=hbase V hn P hP
  refine ⟨weight,hw,hedge,?_⟩
  intro U Γ Color _ _ _ _ hUlo hUhi F π hFdeg hF hπ pR pH D₀ hRlo hRhi hHlo hHhi hDlo hreg hbal q hq hQ s hs hS j hj μ
  have h:=hbase U Γ Color hUlo hUhi F π hFdeg hF hπ pR pH D₀ hRlo hRhi hHlo hHhi hDlo hreg hbal q hq hQ s hs hS j hj
  dsimp only [μ,ordinaryCombinedTriangleEvent]
  exact h
end Oberwolfach
