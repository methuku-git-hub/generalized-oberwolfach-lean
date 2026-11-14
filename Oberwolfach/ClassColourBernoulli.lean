module

public import Oberwolfach.ClassRefinementProduct
public import Oberwolfach.EdgeRetention

@[expose] public section
/-! Each class of a categorical edge-colouring has the correct Bernoulli
membership marginal. Different classes retain their common colour choice. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def classColourMembership {k:ℕ} (a c:Fin k):Bool:=decide (c=a)

theorem categorical_class_membership_law {k:ℕ} (ρ:Fin k→ℝ)
    (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1) (a:Fin k):
    (FiniteLaw.categorical ρ hρ htotal).map (classColourMembership a)=
      FiniteLaw.retentionCoin (ρ a) (hρ a)
        (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith):=by
  apply finiteLaw_ext
  intro b
  cases b with
  | false =>
    simp only [FiniteLaw.map,FiniteLaw.retentionCoin,Bool.false_eq_true,ite_false]
    have hsum:(∑ c:Fin k,((if c=a then ρ c else 0)+(if c=a then 0 else ρ c)))=1:=by
      calc
        _ = ∑ c:Fin k,ρ c:=by
          apply Finset.sum_congr rfl
          intro c _
          by_cases h:c=a <;> simp [h]
        _ = 1:=htotal
    have hs0:(∑ c:Fin k,if c=a then ρ c else 0)=ρ a:=by simp
    rw [Finset.sum_add_distrib,hs0] at hsum
    have hs:(∑ c:Fin k,if c=a then 0 else ρ c)=1-ρ a:=by linarith
    calc
      _ = ∑ c:Fin k,if c=a then 0 else ρ c:=by
        apply Finset.sum_congr rfl
        intro c _
        by_cases h:c=a <;> simp [classColourMembership,FiniteLaw.categorical,h]
      _ = _:=hs
  | true =>
    simp [FiniteLaw.map,FiniteLaw.retentionCoin,classColourMembership,FiniteLaw.categorical]

/-- Membership views of every fixed class have their independent-edge law,
while being projections of the same categorical colouring. -/
theorem categorical_class_membership_product {E:Type} [Fintype E] [DecidableEq E] {k:ℕ}
    (ρ:Fin k→ℝ) (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1) (a:Fin k):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.categorical ρ hρ htotal)).map
      (fun z e=>classColourMembership a (z e))=
      FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin (ρ a) (hρ a)
        (by have h:=Finset.single_le_sum (fun b _=>hρ b) (Finset.mem_univ a);linarith)):=by
  rw [finiteLaw_pi_map (fun _:E=>FiniteLaw.categorical ρ hρ htotal)
    (fun (_:E) c=>classColourMembership a c)]
  congr 1
  funext e
  exact categorical_class_membership_law ρ hρ htotal a
end Oberwolfach
