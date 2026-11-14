module

public import Oberwolfach.RetypedPhysicalDegree
public import Oberwolfach.MarkedFlexibleRetypingInnerSum

@[expose] public section
/-! Local physical change bound for indegree correction with exceptional heads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E:Type} [Fintype V] [Fintype E] [Nonempty V]

theorem marked_indegree_correction_physical_inner_sum
    (tail head:E→V) (M₀:E→Bool) (A:E→Prop) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (I:Finset V) (loc inside:ℝ) (hloc:0≤loc) (hinside:0≤ inside)
    (hlocGlobal:loc≤eta*Fintype.card V) (hinsideGlobal:inside≤(I.card:ℝ)*eta*Fintype.card V)
    (hdevinside:(∑v∈I, |(markedHeadCount head M₀ v:ℝ)-(b:ℝ)|)≤ inside)
    (hdevlocal:∀v,v∉I→|(markedHeadCount head M₀ v:ℝ)-(b:ℝ)|≤loc)
    (hpair:Function.Injective (fun e:E=>(tail e,head e)))
    (hdev:∀v,|(markedHeadCount head M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀v,rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v true:ℝ))
    (hunmarked:∀v,rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v false:ℝ)):
    ∃M:E→Bool,
      (∀v,markedHeadCount head M v=b) ∧ (∀e,M e≠M₀ e→A e) ∧
      (∀v,((physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v:ℝ)≤
        (1+2/rho)*eta*Fintype.card V+1) ∧
      (∀v,v∉I→((physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v:ℝ)≤
        loc+(inside/Fintype.card V+loc)/rho+1):=by
  obtain ⟨M,hM,hA,hhead,hheadlocal,htail⟩:=marked_flexible_retyping_inner_sum tail head M₀ A b rho eta
    hrho heta hetaR I loc inside hloc hinside hdevinside hdevlocal hpair hdev hmarked hunmarked
  let n:ℝ:=Fintype.card V
  have hn:0<n:=by dsimp [n];exact_mod_cast Fintype.card_pos
  let bound:ℝ:=inside/(rho*n)+loc/rho
  have hbound:0≤bound:=by dsimp [bound];positivity
  have heq:inside/(rho*n)+n*(loc/(rho*n))=bound:=by
    dsimp [bound];field_simp
  have htail':∀v,((∑e,if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ)≤bound+1:=by
    intro v
    have hh:=htail v
    change _≤⌈inside/(rho*n)+n*(loc/(rho*n))⌉₊ at hh
    rw [heq] at hh
    have hcast:((∑e,if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ)≤(⌈bound⌉₊:ℕ):=by exact_mod_cast hh
    exact hcast.trans (Nat.ceil_lt_add_one hbound).le
  have hI:((I.card:ℝ)≤n):=by dsimp [n];exact_mod_cast Finset.card_le_univ I
  have hboundglobal:bound≤2*eta*n/rho:=by
    have hscale:=mul_le_mul_of_nonneg_right hI (show 0≤eta*n by positivity)
    have hpart:inside/n≤eta*n:=by
      apply (div_le_iff₀ hn).2
      nlinarith [hinsideGlobal]
    have hsum:inside/n+loc≤2*eta*n:=by linarith
    have hh:=div_le_div_of_nonneg_right hsum hrho.le
    dsimp [bound]
    convert hh using 1 <;> field_simp
  refine ⟨M,hM,hA,?_,?_⟩
  · intro v
    have hd:=retyped_physical_degree_le tail head M M₀ v
    have hd':((physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v:ℝ)≤
      ((∑e,if head e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ)+
      ((∑e,if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ):=by exact_mod_cast hd
    have hh:=hhead v
    have ht:=htail' v
    change _≤eta*n at hh
    change _≤(1+2/rho)*eta*n+1
    have heqglobal:(1+2/rho)*eta*n+1=eta*n+2*eta*n/rho+1:=by ring
    rw [heqglobal]
    linarith [hboundglobal]
  · intro v hv
    have hd:=retyped_physical_degree_le tail head M M₀ v
    have hd':((physicalEdgeGraph (retypedPhysicalEdges tail head M M₀)).degree v:ℝ)≤
      ((∑e,if head e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ)+
      ((∑e,if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ):=by exact_mod_cast hd
    have hh:=hheadlocal v hv
    have ht:=htail' v
    simp only [bound] at ht
    have heq':(inside/n+loc)/rho=inside/(rho*n)+loc/rho:=by ring
    rw [heq']
    calc
      _ ≤ loc+(inside/(rho*n)+loc/rho+1):=hd'.trans (add_le_add hh ht)
      _ = _:=by ring
end Oberwolfach
