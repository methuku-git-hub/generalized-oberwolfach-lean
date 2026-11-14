module

public import Oberwolfach.MarkedFiniteActiveRemainderBalance
public import Oberwolfach.MarkedFiniteCorrectedDomainBound
public import Oberwolfach.MarkedFiniteSupportedBalance

@[expose] public section

/-! All active roots satisfy the quantitative full and inner balance
bounds after the actual sparse correction and two subsequent packings.
The deep packing is charged zero inner loss because it avoids the whole
active inner star; no global small-degree bound for it is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_protected_finite_balance_bounds
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A C₀ EA DA:Finset (E⊕K)) (S CS₀ ES DS:Finset (V×U)) (m:ℕ)
    (I T:Finset V) (J W:Finset U) (hT:T⊆I) (hW:W⊆J)
    (hC₀:C₀⊆A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))
    (hCS₀:CS₀⊆S.filter (fun s=>s.1∈I∧s.2∈J))
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (hE:MarkedRemainderDivisible tail head ktail khead HK EA ES m)
    (hD:MarkedRemainderDivisible tail head ktail khead HK DA DS m)
    (hDA:∀ a∈DA,Sum.elim tail ktail a∉I\T∧Sum.elim head khead a∉I\T)
    (hDS:∀ s∈DS,s.1∉I\T∧s.2∉J\W)
    (εI εT δ₀ δE:ℝ) (hεT:0≤εT) (hδ₀:0≤δ₀) (hδE:0≤δE)
    (hAI:∀ z i,|markedFiniteDomainBalance tail head ktail khead HK A S m I J z i|≤εI)
    (hAT:∀ z i,|markedFiniteDomainBalance tail head ktail khead HK A S m T W z i|≤εT)
    (hC₀A:∀ v,((C₀.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ₀)
    (hC₀R:∀ v,((CS₀.filter (fun s=>s.1=v)).card:ℝ)≤δ₀)
    (hC₀C:∀ u,((CS₀.filter (fun s=>s.2=u)).card:ℝ)≤δ₀)
    (hEA:∀ v,((EA.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δE)
    (hER:∀ v,((ES.filter (fun s=>s.1=v)).card:ℝ)≤δE)
    (hEC:∀ u,((ES.filter (fun s=>s.2=u)).card:ℝ)≤δE):
    let C:=(A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\C₀
    let CS:=(S.filter (fun s=>s.1∈I∧s.2∈J))\CS₀
    let KA:=C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun s=>s.1∈T∨s.2∈W);
    EA⊆A\KA→ES⊆S\KS→DA⊆(A\KA)\EA→DS⊆(S\KS)\ES→
    ∀ (z:V⊕U),Sum.elim (fun v=>v∉T) (fun u=>u∉W) z→∀ i:Fin 4,
    |markedFiniteBalance tail head ktail khead HK (((A\KA)\EA)\DA) (((S\KS)\ES)\DS) m z i|
      ≤εT+(m+2)*δ₀ ∧
    |markedFiniteDomainBalance tail head ktail khead HK (((A\KA)\EA)\DA) (((S\KS)\ES)\DS) m (I\T) (J\W) z i|
      ≤εI+εT+(m+2)*δE:=by
  intro C CS KA KS hEAsub hESsub hDAsub hDSsub z hz i
  have hC:C⊆A:=(Finset.sdiff_subset).trans (Finset.filter_subset _ _)
  have hCS:CS⊆S:=(Finset.sdiff_subset).trans (Finset.filter_subset _ _)
  obtain ⟨hfull,hinner⟩:=marked_finite_active_remainder_balances tail head ktail khead HK A C EA DA S CS ES DS m
    I T J W hT hW hC hCS hdiv hE hD hDA hDS hEAsub hESsub hDAsub hDSsub z hz i
  constructor
  · rw [hfull,abs_neg]
    by_cases hinside:Sum.elim (fun v=>v∈I) (fun u=>u∈J) z
    · exact marked_finite_corrected_inner_domain_bound tail head ktail khead HK A C₀ S CS₀ m
        I T J W hT hW hC₀ hCS₀ εT δ₀ hδ₀ hC₀A hC₀R hC₀C z hinside i (hAT z i)
    · have hout:Sum.elim (fun v=>v∉I) (fun u=>u∉J) z:=by cases z <;> exact hinside
      rw [markedFiniteDomainBalance_zero_of_support tail head ktail khead HK C CS m I J
        (fun a ha=>(Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2)
        (fun s hs=>(Finset.mem_filter.mp (Finset.mem_sdiff.mp hs).1).2) T W z hout i,abs_zero]
      positivity
  · exact marked_finite_active_inner_error tail head ktail khead HK A EA _ S ES _ m I T J W z i
      hinner εI εT δE hδE (hAI z i) (hAT z i) hEA hER hEC

end Oberwolfach
