module

public import Oberwolfach.MarkedFiniteFullBalanceBridge

@[expose] public section
/-! Extract the exact row and column spoke sizes from full finite
wheel-divisibility for disjoint ordinary and marked spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_divisible_full_spoke_size_identities
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (m:ℕ)
    (hdis:∀v u,¬(H₀ v u∧HK v u))
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m):
    (∀v,((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)=
      ((Finset.univ.filter (fun u=>H₀ v u)).card:ℝ)+((Finset.univ.filter (fun u=>HK v u)).card:ℝ)) ∧
    (∀u,(Finset.univ.filter (fun v=>H₀ v u)).card=m*(Finset.univ.filter (fun v=>HK v u)).card):=by
  constructor
  · intro v
    have hS:=finite_spoke_relation_row_count (fun v u=>H₀ v u∨HK v u) v
    have hs:((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)=
        (((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter (fun s=>s.1=v)).card:ℝ):=by exact_mod_cast hdiv.row v
    have hS':(((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter (fun s=>s.1=v)).card:ℝ)=
        ∑u,if H₀ v u∨HK v u then (1:ℝ) else 0:=by
      convert hS using 1 <;> congr!
    rw [hs,hS',←Finset.sum_boole,←Finset.sum_boole,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have hh:=hdis v u
    by_cases h0:H₀ v u <;> by_cases hk:HK v u <;> simp_all
  · intro u
    have h0:((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter
        (fun s=>s.2=u∧¬HK s.1 s.2))=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2)).filter (fun s=>s.2=u):=by
      ext s
      have hh:=hdis s.1 s.2
      simp only [Finset.mem_filter,Finset.mem_univ,true_and];tauto
    have h1:((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter
        (fun s=>s.2=u∧HK s.1 s.2))=(Finset.univ.filter (fun s:V×U=>HK s.1 s.2)).filter (fun s=>s.2=u):=by
      ext s
      simp only [Finset.mem_filter,Finset.mem_univ,true_and];tauto
    have hh:=hdiv.hub u
    rw [h0,h1] at hh
    have hr:(((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2)).filter (fun s=>s.2=u)).card:ℝ)=
        (m:ℝ)*(((Finset.univ.filter (fun s:V×U=>HK s.1 s.2)).filter (fun s=>s.2=u)).card:ℝ):=by exact_mod_cast hh
    rw [finite_spoke_relation_col_count,finite_spoke_relation_col_count,Finset.sum_boole,Finset.sum_boole] at hr
    exact_mod_cast hr
end Oberwolfach
