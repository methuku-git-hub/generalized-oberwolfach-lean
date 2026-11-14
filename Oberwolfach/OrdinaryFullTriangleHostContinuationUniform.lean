module

public import Oberwolfach.OrdinaryUniformTriangleHostContinuation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_full_triangle_host_continuation_uniform
    (d:ℕ) (hd:2≤d) (θ α pstar ω βP ηP ηH L:ℝ)
    (hθ:cycleThreshold 3≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4)
    (hβhub:βP≤ω*pstar^9/4) (hηP:0<ηP) (hηH:0<ηH) (hL:0≤L):
    ∃ (k:ℕ) (βH c B ε:ℝ),5≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ 0<ε ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ P:SimpleGraph V,(∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight:OrdinaryCycle P 3→ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(3-2)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
    ordinaryUniformTriangleHostContinuation d k hd P θ α pstar ω βP ηP ηH L βH c B ε hpstar weight := by
  obtain ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,N,hbase⟩:=ordinary_full_host_and_triangle_inputs_named
    d hd θ α pstar ω βP ηP ηH L hθ hα hα1 hθ1 hpstar hpstar1 hω
    hβP hβmax hβhub hηP hηH hL
  refine ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,N,?_⟩
  intro V _ _ hn P hP
  obtain ⟨weight,hw,hedge,hcont⟩:=hbase V hn P hP
  exact ⟨weight,hw,hedge,hcont⟩
end Oberwolfach
