module

public import Oberwolfach.ShellPermutation

@[expose] public section
/-! A two-domain triangle construction can use a single permutation on the
sum type without changing its action on rim vertices. The hub type only needs
to be large enough for a long cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_permutation_no_short_returns {U:Type} [Fintype U] (h:ℕ)
    (hcard:h≤Fintype.card U):
    ∃τ:Equiv.Perm U,∀u k,0<k→k<h→(τ^k) u≠u:=by
  classical
  obtain ⟨τ,_,hp⟩:=fibre_cycles (fun _:U=>())
  refine ⟨τ,?_⟩
  intro u k hk hkh he
  have hd:Fintype.card U∣k:=by simpa using (hp u k).mp he
  exact (not_lt_of_ge (hcard.trans (Nat.le_of_dvd hk hd))) hkh

theorem ordinary_two_domain_permutation {V U:Type} [Fintype V] [Fintype U]
    (π:Equiv.Perm V) (h:ℕ) (hU:h≤Fintype.card U)
    (hπ:∀v k,0<k→k<h→(π^k) v≠v):
    ∃σ:Equiv.Perm (V⊕U),
      (∀v k,(σ^k) (Sum.inl v)=Sum.inl ((π^k) v)) ∧
      (∀z k,0<k→k<h→(σ^k) z≠z):=by
  obtain ⟨τ,hτ⟩:=finite_permutation_no_short_returns h hU
  let σ:Equiv.Perm (V⊕U):=Equiv.sumCongr π τ
  have hl (v:V) (k:ℕ):(σ^k) (Sum.inl v)=Sum.inl ((π^k) v):=by
    induction k with
    | zero=>rfl
    | succ k ih=>
      rw [pow_succ',Equiv.Perm.mul_apply,ih,pow_succ',Equiv.Perm.mul_apply]
      rfl
  have hr (u:U) (k:ℕ):(σ^k) (Sum.inr u)=Sum.inr ((τ^k) u):=by
    induction k with
    | zero=>rfl
    | succ k ih=>
      rw [pow_succ',Equiv.Perm.mul_apply,ih,pow_succ',Equiv.Perm.mul_apply]
      rfl
  refine ⟨σ,hl,?_⟩
  intro z k hk hkh he
  cases z with
  | inl v=>exact hπ v k hk hkh (Sum.inl.inj ((hl v k).symm.trans he))
  | inr u=>exact hτ u k hk hkh (Sum.inr.inj ((hr u k).symm.trans he))
end Oberwolfach
