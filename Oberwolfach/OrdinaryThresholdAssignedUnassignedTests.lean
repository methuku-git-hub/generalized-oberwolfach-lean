module

public import Oberwolfach.OrdinaryAssignedUnassignedTestsContinuation
public import Oberwolfach.OrdinaryThresholdAssignedFullMatchingTests

@[expose] public section
/-! The actual ordinary threshold construction with its same-sample
shifted-closing approximate wheel-load tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryThresholdUnassignedTestsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_threshold_assigned_unassigned_tests
    (IM IO:Type) [Fintype IM] [Fintype IO] (mM:ℕ) (mO:IO→ℕ)
    (BM tM:ℝ) (BO tO:IO→ℝ) (hmM:3≤mM) (hmO:∀i,2≤mO i)
    (hBM:0<BM) (htM:0<tM) (hBO:∀i,0<BO i) (htO:∀i,0<tO i)
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (θ α pstar ω βP ηP row ηH L:ℝ)
    (hθ:cycleThreshold (m+1)≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤(α/2)*pstar^2*pstar^2)
    (hβhub:βP≤ω*pstar^(m+7)/4) (hηP:0<ηP) (hrow:0<row)
    (hrowmax:row≤pstar^(m+7)/2) (hηH:0<ηH) (hL:0≤L)
    (δ χ:ℝ) (hδ:0<δ) (hχ:0<χ):
    ∃ (k:ℕ) (βH c B ε αpack:ℝ),m+3≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ 0<ε ∧ 0<αpack ∧ ∃N:ℕ,
    ∀n≥N,∀P:SimpleGraph (Fin n),(∀v,(θ+α)*n≤(P.degree v:ℝ))→
    ∃weight:OrdinaryCycle P (m+1)→ℝ,
      (∀C,c/(n:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(n:ℝ)^((m+1)-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
      OrdinaryAssignedUnassignedTestsContinuation IM IO mM mO BM tM BO tO δ χ (α/2) αpack m d k hm hd P θ α pstar ω βP ηP row ηH L βH c B ε weight :=by
  obtain ⟨k,βH,c,B,ε,αpack,hk,hβH,hc,hB,hε,hαpack,Nhost,hHost⟩:=ordinary_threshold_assigned_full_matching_tests
    IM IO mM mO BM tM BO tO hmM hmO hBM htM hBO htO m d hm hd θ α pstar ω βP ηP row ηH L hθ hα hα1 hθ1 hpstar hpstar1 hω hβP hβmax hβhub hηP hrow hrowmax hηH hL δ (χ/2) hδ (by positivity)
  obtain ⟨Nextra,hExtra⟩:=ordinary_assigned_unassigned_tests_continuation IM IO mM mO BM tM BO tO δ χ (α/2) αpack m d k hm hd hχ
  refine ⟨k,βH,c,B,ε,αpack,hk,hβH,hc,hB,hε,hαpack,max Nhost Nextra,?_⟩
  intro n hn P hP
  obtain ⟨weight,hw,hedge,hcont⟩:=hHost n (by omega) P hP
  refine ⟨weight,hw,hedge,?_⟩
  exact hExtra n (by omega) P θ α pstar ω βP ηP row ηH L βH c B ε weight hcont
end Oberwolfach
