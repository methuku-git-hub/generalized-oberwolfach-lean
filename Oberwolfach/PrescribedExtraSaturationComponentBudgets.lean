module

public import Oberwolfach.PrescribedAllComponentBudgets

@[expose] public section
/-! Reserve room for a second saturation set by running the existing
component budget with half of the extension-list density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_extra_saturation_component_budgets
    {X V:Type} [DecidableEq X] [DecidableEq V]
    (Q A:Finset X) (as:List X) (ha:as.Nodup)
    (hsub:A∪as.toFinset⊆Q) (hdis:Disjoint A as.toFinset)
    (f:X→V) (S Sextra:Finset V) (M β δ n:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/200)^2)
    (hnβ:200/β≤n) (hQ:(Q.card:ℝ)≤δ*n)
    (hS:(S.card:ℝ)≤Real.sqrt δ*n) (hExtra:(Sextra.card:ℝ)≤β*n/4)
    (hM0:0≤M) (hM:M≤8*Real.sqrt δ*n):
    let b:ℝ:=(A.image f∪(S∪Sextra)).card;
    b+as.length+2+M<β*n ∧ b+as.length+1+M<β*n ∧
    b+as.length+2+2*M<β*n ∧ b+(as.length+1:ℕ)+2+2*M<β*n :=by
  intro b
  have hhalf:δ≤((β/2)/100)^2:=by convert hδbound using 1 <;> ring
  have hnHalf:100/(β/2)≤n:=by convert hnβ using 1 <;> ring
  have hbase:=prescribed_all_component_budgets Q A as ha hsub hdis f S M (β/2) δ n
    (by positivity) (by linarith) hδ hhalf hnHalf hQ hS hM0 hM
  have hc:(A.image f∪(S∪Sextra)).card≤(A.image f∪S).card+Sextra.card:=by
    rw [←Finset.union_assoc]
    exact Finset.card_union_le _ _
  have hc':(b:ℝ)≤((A.image f∪S).card:ℝ)+Sextra.card:=by
    dsimp only [b]
    exact_mod_cast hc
  have hn0:0≤n:=by
    have hh:0≤200/β:=by positivity
    linarith
  have hβn:0≤β*n:=mul_nonneg hβ.le hn0
  dsimp only at hbase
  push_cast at *
  rcases hbase with ⟨h1,h2,h3,h4⟩
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [hc',hExtra,hβn]
end Oberwolfach
