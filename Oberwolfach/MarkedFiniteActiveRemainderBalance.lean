module

public import Oberwolfach.MarkedFiniteActiveStarBalance
public import Oberwolfach.MarkedFiniteDomainBalanceBounds

@[expose] public section

/-! Exact full and inner balance of the host left by the prescribed
packing and deep-star packing. The reserved star is restored only later;
its balance is not assumed to vanish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_finite_active_remainder_balances
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A C EA DA:Finset (E⊕K)) (S CS ES DS:Finset (V×U)) (m:ℕ)
    (X T:Finset V) (Z W:Finset U) (hT:T⊆X) (hW:W⊆Z)
    (hC:C⊆A) (hCS:CS⊆S)
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (hE:MarkedRemainderDivisible tail head ktail khead HK EA ES m)
    (hD:MarkedRemainderDivisible tail head ktail khead HK DA DS m)
    (hDA:∀ a∈DA,Sum.elim tail ktail a∉X\T∧Sum.elim head khead a∉X\T)
    (hDS:∀ s∈DS,s.1∉X\T∧s.2∉Z\W):
    let KA:=C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun s=>s.1∈T∨s.2∈W);
    EA⊆A\KA→ES⊆S\KS→DA⊆(A\KA)\EA→DS⊆(S\KS)\ES→
    ∀ (z:V⊕U),Sum.elim (fun v=>v∉T) (fun u=>u∉W) z→∀ i:Fin 4,
    markedFiniteBalance tail head ktail khead HK (((A\KA)\EA)\DA) (((S\KS)\ES)\DS) m z i=
      -markedFiniteDomainBalance tail head ktail khead HK C CS m T W z i∧
    markedFiniteDomainBalance tail head ktail khead HK (((A\KA)\EA)\DA) (((S\KS)\ES)\DS) m (X\T) (Z\W) z i=
      markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i-
      markedFiniteDomainBalance tail head ktail khead HK A S m T W z i-
      markedFiniteDomainBalance tail head ktail khead HK EA ES m (X\T) (Z\W) z i:=by
  intro KA KS hEA hES hDAsub hDSsub z hz i
  have hKA:KA⊆A:=(Finset.filter_subset _ _).trans hC
  have hKS:KS⊆S:=(Finset.filter_subset _ _).trans hCS
  have hKzero:=markedFiniteDomainBalance_star_active_zero tail head ktail khead HK C CS m X T Z W z hz i
  have hDzero:=markedFiniteDomainBalance_zero_of_avoids tail head ktail khead HK DA DS m (X\T) (Z\W) hDA hDS z i
  constructor
  · rw [markedFiniteBalance_subtract_divisible _ _ _ _ _ _ _ _ _ _ hDAsub hDSsub hD,
      markedFiniteBalance_subtract_divisible _ _ _ _ _ _ _ _ _ _ hEA hES hE,
      markedFiniteBalance_sdiff _ _ _ _ _ _ _ _ _ _ hKA hKS,
      (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hdiv z i,zero_sub]
    exact congrArg Neg.neg (markedFiniteBalance_star_outside tail head ktail khead HK C CS m T W z hz i)
  · rw [markedFiniteDomainBalance_sdiff _ _ _ _ _ _ _ _ _ _ _ _ hDAsub hDSsub,
      markedFiniteDomainBalance_sdiff _ _ _ _ _ _ _ _ _ _ _ _ hEA hES,
      markedFiniteDomainBalance_sdiff _ _ _ _ _ _ _ _ _ _ _ _ hKA hKS]
    change _-markedFiniteDomainBalance tail head ktail khead HK
      (C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))
      (CS.filter (fun s=>s.1∈T∨s.2∈W)) m (X\T) (Z\W) z i-_-_=_
    rw [hKzero,hDzero,sub_zero,sub_zero,
      markedFiniteDomainBalance_domain_sdiff _ _ _ _ _ _ _ _ X T Z W hT hW]

theorem marked_finite_active_inner_error
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A EA R:Finset (E⊕K)) (S ES RS:Finset (V×U)) (m:ℕ)
    (X T:Finset V) (Z W:Finset U) (z:V⊕U) (i:Fin 4)
    (hidentity:markedFiniteDomainBalance tail head ktail khead HK R RS m (X\T) (Z\W) z i=
      markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i-
      markedFiniteDomainBalance tail head ktail khead HK A S m T W z i-
      markedFiniteDomainBalance tail head ktail khead HK EA ES m (X\T) (Z\W) z i)
    (εX εT δ:ℝ) (hδ:0≤δ)
    (hX:|markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i|≤εX)
    (hT:|markedFiniteDomainBalance tail head ktail khead HK A S m T W z i|≤εT)
    (hEA:∀ v,((EA.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ)
    (hER:∀ v,((ES.filter (fun s=>s.1=v)).card:ℝ)≤δ)
    (hEC:∀ u,((ES.filter (fun s=>s.2=u)).card:ℝ)≤δ):
    |markedFiniteDomainBalance tail head ktail khead HK R RS m (X\T) (Z\W) z i|≤εX+εT+(m+2)*δ:=by
  have he:=markedFiniteDomainBalance_bound tail head ktail khead HK EA ES m (X\T) (Z\W) δ hδ hEA hER hEC z i
  rw [hidentity]
  exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hX hT)) he)

end Oberwolfach
