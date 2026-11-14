module

public import Oberwolfach.OrdinaryUniformHostContinuation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_full_host_continuation_uniform
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (θ α pstar ω βP ηP row ηH L:ℝ)
    (hθ:cycleThreshold (m+1)≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤(α/2)*pstar^2*pstar^2)
    (hβhub:βP≤ω*pstar^(m+7)/4) (hηP:0<ηP) (hrow:0<row)
    (hrowmax:row≤pstar^(m+7)/2) (hηH:0<ηH) (hL:0≤L):
    ∃ (k:ℕ) (βH c B ε:ℝ),m+3≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ 0<ε ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ P:SimpleGraph V,(∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight:OrdinaryCycle P (m+1)→ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^((m+1)-2)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
    ordinaryUniformHostContinuation m d k hm hd P θ α pstar ω βP ηP row ηH L βH c B ε hpstar weight := by
  obtain ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,N,hbase⟩:=ordinary_full_host_and_absorber_inputs_named
    m d hm hd θ α pstar ω βP ηP row ηH L hθ hα hα1 hθ1 hpstar hpstar1 hω
    hβP hβmax hβhub hηP hrow hrowmax hηH hL
  refine ⟨k,βH,c,B,ε,hk,hβH,hc,hB,hε,N,?_⟩
  intro V _ _ hn P hP
  obtain ⟨weight,hw,hedge,hcont⟩:=hbase V hn P hP
  exact ⟨weight,hw,hedge,hcont⟩
end Oberwolfach
