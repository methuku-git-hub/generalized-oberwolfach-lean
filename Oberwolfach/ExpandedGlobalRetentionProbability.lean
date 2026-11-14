module

public import Oberwolfach.RawMarkedRetentionLocalEvent
public import Oberwolfach.MarkedExpandedRetainedProjection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Global row and hub retention can be requested on the same expanded
sample, with arbitrarily small failure probability. -/
theorem expanded_global_retention_high_probability
    (d:ℕ) (hd:2≤d) (pRet ζ c failure:ℝ)
    (hp:0<pRet) (hζ:0<ζ) (hc:0<c) (hfailure:0<failure):
    ∃m₀ N:ℕ,1≤m₀ ∧ 1≤N ∧ ∀(V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U],
    N≤Fintype.card V → m₀≤Fintype.card V → Fintype.card U≤Fintype.card V →
    c*(Fintype.card V:ℝ)≤Fintype.card U →
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp₁:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t₀:ℝ) (hq0:∀w,q w false=t₀) (hmass:pRet*Fintype.card V≤t₀*Fintype.card U),
    let Ret:=fun raw:RawMarkedOutcome V U Bool Bool=>StartRetentionOutcome
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome V U Bool Bool=>startRetentionLaw
      (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp₁ hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z:Σω,Ret (f ω)=>
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2) :=by
  obtain ⟨m₀,N,hm₀,hN,hRet⟩:=raw_marked_retention_local_event d hd pRet ζ c failure hp hζ hc hfailure
  refine ⟨m₀,N,hm₀,hN,?_⟩
  intro V U _ _ _ _ _ hn hm hu hsize π p k p₂ k₂ u hp₁ hk hp₂ hk₂ hu0 hsum q hq hQ s hs hS hnoshort t₀ hq0 hmass Ret ν μ f
  let A:Unit→Finset V:=fun _=>Finset.univ
  let H:Unit→Finset U:=fun _=>Finset.univ
  have hmin:∀i∈(Finset.univ:Finset Unit),m₀≤(A i).card:=by simpa [A]
  have hinj:Set.InjOn (fun i=>(A i).card) (Finset.univ:Finset Unit):=by intro i hi j hj hij;exact Subsingleton.elim i j
  have hHup:∀i∈(Finset.univ:Finset Unit),(H i).card≤(A i).card:=by simpa [A,H] using hu
  have hHlo:∀i∈(Finset.univ:Finset Unit),c*((A i).card:ℝ)≤(H i).card:=by simpa [A,H] using hsize
  have hInv:∀i∈(Finset.univ:Finset Unit),∀x,π x∈A i↔x∈A i:=by simp [A]
  have hphys:2*p+2*k≤1:=by linarith
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false=>
    RetainedRestrictionLocalGood π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
      Finset.univ Finset.univ ζ z.2
  have hbase:=hRet V U Bool Bool hn hu Unit Finset.univ A H hmin hinj hHup hHlo π p k hp₁ hk hphys hnoshort q hq hQ s hs hS false t₀ hq0 hmass hInv
  have hbase':1-failure≤(rawMarkedRetentionLaw π d hd false p k hp₁ hk hphys q hq hQ s hs hS).probability E:=by
    simpa only [A,H,E,Finset.mem_univ,forall_const] using hbase
  have hproj:=raw_expanded_marked_retained_projection_probability p k p₂ k₂ u hp₁ hk hp₂ hk₂ hu0 hsum d hd q hq hQ s hs hS Ret ν E
  unfold rawMarkedRetentionLaw at hbase'
  rw [←hproj] at hbase'
  apply hbase'.trans
  apply finiteLaw_probability_mono
  intro z hz i
  exact ⟨fun w=>hz.1 w (Finset.mem_univ w),fun x=>hz.2 x (Finset.mem_univ x)⟩
end Oberwolfach
