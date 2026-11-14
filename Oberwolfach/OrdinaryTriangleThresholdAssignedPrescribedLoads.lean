module

public import Oberwolfach.OrdinaryTriangleAssignedPrescribedLoadsContinuation

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
local instance (priority := high) ordinaryTriangleThresholdLoadsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_triangle_threshold_assigned_prescribed_loads
    (IM IO:Type) [Fintype IM] [Fintype IO] (mM:ℕ) (mO:IO→ℕ)
    (BM tM:ℝ) (BO tO:IO→ℝ) (hmM:3≤mM) (hmO:∀i,2≤mO i)
    (hBM:0<BM) (htM:0<tM) (hBO:∀i,0<BO i) (htO:∀i,0<tO i)
    (d:ℕ) (hd:2≤d) (θ α pstar ω βP ηP ηH L:ℝ)
    (hθ:cycleThreshold 3≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4)
    (hβhub:βP≤ω*pstar^9/4) (hηP:0<ηP) (hηH:0<ηH) (hL:0≤L)
    (δ χ:ℝ) (hδ:0<δ) (hχ:0<χ):
    ∃ (k:ℕ) (βH c B ε αpack:ℝ),5≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ 0<ε ∧ 0<αpack ∧ ∃N:ℕ,
    ∀n≥N,∀P:SimpleGraph (Fin n),(∀v,(θ+α)*n≤(P.degree v:ℝ))→
    ∃weight:OrdinaryCycle P 3→ℝ,
      (∀C,c/(n:ℝ)^(3-2)≤weight C ∧ weight C≤B/(n:ℝ)^(3-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
      OrdinaryTriangleAssignedPrescribedLoadsContinuation IM IO mM mO BM tM BO tO δ χ (α/2) αpack d k hd P θ α pstar ω βP ηP ηH L βH c B ε weight :=by
  obtain ⟨k,βH,c,B,ε,αpack,hk,hβH,hc,hB,hε,hαpack,Nhost,hHost⟩:=ordinary_triangle_threshold_assigned_prescribed_host
    d hd θ α pstar ω βP ηP ηH L hθ hα hα1 hθ1 hpstar hpstar1 hω hβP hβmax hβhub hηP hηH hL δ (χ/2) hδ (by positivity)
  obtain ⟨Nload,hLoad⟩:=ordinary_triangle_assigned_prescribed_loads_continuation IM IO mM mO BM tM BO tO δ χ (α/2) αpack d k hd hmM hmO hBM htM hBO htO hχ
  refine ⟨k,βH,c,B,ε,αpack,hk,hβH,hc,hB,hε,hαpack,max Nhost Nload,?_⟩
  intro n hn P hP
  obtain ⟨weight,hw,hedge,hcont⟩:=hHost n (by omega) P hP
  refine ⟨weight,hw,hedge,?_⟩
  exact hLoad n (by omega) P θ α pstar ω βP ηP ηH L βH c B ε weight hcont
end Oberwolfach
