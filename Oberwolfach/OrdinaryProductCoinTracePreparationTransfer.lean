module

public import Oberwolfach.OrdinarySharedSampleTracePreparationTransfer
public import Oberwolfach.FiniteProductRegrouping

@[expose] public section
/-! Transfer a high-probability trace certificate from the expanded sample
and the same auxiliary reference coins to the original retention marginal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) productCoinTraceTransferFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_product_coin_trace_preparation_transfer
    {n q r:ℕ} {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (a:U→Γ→ℝ) (ha:∀w j,0≤a w j) (hA:∀w,∑j,a w j≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑j,a w j))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool))
    (E:((Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 (Fin n)→Bool))→Prop)
    (b:ℝ)
    (hE:b≤(((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd a ha hA s hs hS)).sigma ν).prod κcoins).probability E)
    (hcomplete:∀z,E z→OrdinaryNaturalTraceCertificate (r:=r) P (longPhysicalStateGraph P z.1.1 {0,1,2,3,4}) I ξ B F C)
    (ρ:ℝ) (hρ:ρ=2*p+2*k+2*p₂+2*k₂+u) (hρ0:0≤ρ) (hρ1:ρ≤1):
    b≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ hρ0 hρ1)).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd a ha hA s hs hS)
  let Trace:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop:=
    fun z=>(OrdinaryNaturalTraceCertificate (r:=r) P (longPhysicalStateGraph P z.1 {0,1,2,3,4}) I ξ B F C)
  have hTrace:b≤(μ.sigma ν).probability Trace:=by
    rw [←finiteLaw_prod_first_probability (μ.sigma ν) κcoins Trace]
    apply hE.trans
    apply finiteLaw_probability_mono
    intro z hz
    exact hcomplete z hz
  have hh:=ordinary_shared_sample_trace_preparation_transfer P I ξ B F hF C hr hsize
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd a ha hA s hs hS ν Trace b hTrace (fun z hz=>hz)
  subst ρ
  convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
