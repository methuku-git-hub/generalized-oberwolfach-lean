module

public import Oberwolfach.MarkedFiniteDomainBalanceBridge

@[expose] public section

/-! The constructed finite balance estimates supply the four quantitative
balance inputs of active cover-down, at every ambient row and hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

private theorem protected_active_balance_margins
    (r:ℕ) (n nA m theta mu etaE errI errT:ℝ)
    (hn:0≤n) (hnA:n/2≤nA) (hm:m≤n) (ht:0≤theta) (hmu:0≤mu)
    (hI:errI≤theta*n/8) (hT:errT≤theta*n/8)
    (hcor:(r+6:ℝ)*mu≤theta/8)
    (hpack:(r+6:ℝ)*(96+3*(r+5:ℝ))*etaE≤theta/4):
    errT+(r+6:ℝ)*(mu*m)≤theta*nA∧
    errI+errT+(r+6:ℝ)*(4*(24*etaE*n)+3*(r+5:ℝ)*etaE*n)≤theta*nA:=by
  have hcorN:=mul_le_mul_of_nonneg_right hcor hn
  have hm':=mul_le_mul_of_nonneg_left hm (show 0≤(r+6:ℝ)*mu by positivity)
  have hpackN:=mul_le_mul_of_nonneg_right hpack hn
  have hA:=mul_le_mul_of_nonneg_left hnA ht
  have htn:0≤theta*n:=mul_nonneg ht hn
  exact ⟨by nlinarith only [hT,hcorN,hm',hA,htn],
    by nlinarith only [hI,hT,hpackN,hA]⟩

theorem marked_active_balance_parameter_allowances (r:ℕ) (theta:ℝ) (ht:0<theta):
    ∃ mu0 etaE0:ℝ,0<mu0∧0<etaE0∧∀ mu etaE:ℝ,mu≤mu0→etaE≤etaE0→
      (r+6:ℝ)*mu≤theta/8∧(r+6:ℝ)*(96+3*(r+5:ℝ))*etaE≤theta/4:=by
  obtain ⟨mu0,hmu,hmuB⟩:=exists_pos_mul_lt (show 0<theta/8 by positivity) (r+6:ℝ)
  obtain ⟨etaE0,hetaE,hetaB⟩:=exists_pos_mul_lt (show 0<theta/4 by positivity) ((r+6:ℝ)*(96+3*(r+5:ℝ)))
  refine ⟨mu0,etaE0,hmu,hetaE,?_⟩
  intro mu etaE hm he
  exact ⟨(mul_le_mul_of_nonneg_left hm (by positivity)).trans hmuB.le,
    (mul_le_mul_of_nonneg_left he (by positivity)).trans hetaB.le⟩

variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_protected_active_balance_inputs
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (hd:∀ v u,¬(H₀ v u∧HK v u)) (r:ℕ) (X:Finset V) (Z:Finset U)
    (n m theta mu etaE errI errT:ℝ)
    (hn:0≤n) (hnA:n/2≤Fintype.card V) (hm:m≤n) (ht:0≤theta) (hmu:0≤mu)
    (hI:errI≤theta*n/8) (hT:errT≤theta*n/8)
    (hcor:(r+6:ℝ)*mu≤theta/8)
    (hpack:(r+6:ℝ)*(96+3*(r+5:ℝ))*etaE≤theta/4)
    (hbalance:∀ (z:V⊕U) (i:Fin 4),
      |markedFiniteBalance tail head ktail khead HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) (r+4) z i|
        ≤errT+((r+4:ℕ)+2)*(mu*m)∧
      |markedFiniteDomainBalance tail head ktail khead HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) (r+4) X Z z i|
        ≤errI+errT+((r+4:ℕ)+2)*(4*(24*etaE*n)+3*(r+5)*etaE*n)):
    let a:=fun z j=>((markedBalanceTermSet tail head ktail khead H₀ HK z j).card:ℝ)
    let c:=fun z j=>(((markedBalanceTermSet tail head ktail khead H₀ HK z j).filter (fun e=>
      (if markedActiveAuxTail tail ktail H₀ HK e=z then markedActiveAuxHead head khead H₀ HK e
        else markedActiveAuxTail tail ktail H₀ HK e)∈ordinaryInnerVertices X Z)).card:ℝ);
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (r+4) (a (Sum.inl v)) i.castSucc|≤theta*Fintype.card V)∧
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (r+4) (c (Sum.inl v)) i.castSucc|≤theta*Fintype.card V)∧
    (∀ u,|markedSixDegreeBalance (r+4) (a (Sum.inr u)) 3|≤theta*Fintype.card V)∧
    (∀ u,|markedSixDegreeBalance (r+4) (c (Sum.inr u)) 3|≤theta*Fintype.card V):=by
  intro a c
  obtain ⟨hfull,hinner⟩:=protected_active_balance_margins r n (Fintype.card V) m theta mu etaE errI errT
    hn hnA hm ht hmu hI hT hcor hpack
  have hbalance':∀ (z:V⊕U) (i:Fin 4),
      |markedFiniteBalance tail head ktail khead HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) (r+4) z i|≤theta*Fintype.card V∧
      |markedFiniteDomainBalance tail head ktail khead HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) (r+4) X Z z i|≤theta*Fintype.card V:=by
    intro z i
    have hb:=hbalance z i
    have hf':errT+((r+4:ℕ)+2:ℕ)*(mu*m)≤theta*Fintype.card V:=by
      convert hfull using 1 <;> push_cast <;> ring
    have hi':errI+errT+((r+4:ℕ)+2:ℕ)*(4*(24*etaE*n)+3*(r+5)*etaE*n)≤theta*Fintype.card V:=by
      convert hinner using 1 <;> push_cast <;> ring
    exact ⟨hb.1.trans (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hf'),
      hb.2.trans (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hi')⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro v i
    rw [←markedFiniteBalance_full_row tail head ktail khead H₀ HK hd (r+4) v i]
    exact (hbalance' (Sum.inl v) i.castSucc).1
  · intro v i
    rw [←markedFiniteDomainBalance_row tail head ktail khead H₀ HK hd (r+4) X Z v i]
    exact (hbalance' (Sum.inl v) i.castSucc).2
  · intro u
    rw [←markedFiniteBalance_full_hub tail head ktail khead H₀ HK hd (r+4) u]
    exact (hbalance' (Sum.inr u) 3).1
  · intro u
    rw [←markedFiniteDomainBalance_hub tail head ktail khead H₀ HK hd (r+4) X Z u]
    exact (hbalance' (Sum.inr u) 3).2

end Oberwolfach
