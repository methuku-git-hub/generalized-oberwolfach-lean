module

public import Oberwolfach.SimpleWalkConcatSupport

@[expose] public section
/-! Finite chains of simple walks with disjoint initial support concatenate
 to a simple walk, with exact length and vertex support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

inductive SimpleWalkChain {V:Type*} (G:SimpleGraph V):V→V→Type _
  | nil (v:V):SimpleWalkChain G v v
  | cons {a b c:V} (p:G.Walk a b) (q:SimpleWalkChain G b c):SimpleWalkChain G a c

namespace SimpleWalkChain
variable {V:Type*} [DecidableEq V] {G:SimpleGraph V}

def toWalk : {a b:V} → SimpleWalkChain G a b → G.Walk a b
  | _,_,.nil _ => .nil
  | _,_,.cons p q => p.append q.toWalk

def initials : {a b:V} → SimpleWalkChain G a b → Finset V
  | _,_,.nil _ => ∅
  | _,_,.cons p q => p.support.dropLast.toFinset ∪ q.initials

def totalLength : {a b:V} → SimpleWalkChain G a b → ℕ
  | _,_,.nil _ => 0
  | _,_,.cons p q => p.length+q.totalLength

theorem mem_toWalk_support {a b:V} (q:SimpleWalkChain G a b) (x:V):
    x∈q.toWalk.support ↔ x=b ∨ x∈q.initials := by
  induction q with
  | nil v => simp [toWalk,initials]
  | cons p q ih =>
    simp only [toWalk,SimpleGraph.Walk.support_append_eq_support_dropLast_append,List.mem_append,
      initials,Finset.mem_union,List.mem_toFinset,ih]
    tauto

theorem toWalk_length {a b:V} (q:SimpleWalkChain G a b):q.toWalk.length=q.totalLength := by
  induction q with
  | nil v => rfl
  | cons p q ih => simp [toWalk,totalLength,ih]

inductive Compatible : {a b:V} → SimpleWalkChain G a b → Prop
  | nil (v:V):Compatible (.nil v)
  | cons {a b c:V} (p:G.Walk a b) (q:SimpleWalkChain G b c)
      (hp:p.IsPath) (hq:Compatible q)
      (hdis:∀x∈p.support.dropLast,x∉q.initials ∧ x≠c):Compatible (.cons p q)

theorem toWalk_isPath {a b:V} {q:SimpleWalkChain G a b} (h:Compatible q):q.toWalk.IsPath := by
  induction h with
  | nil v => exact SimpleGraph.Walk.IsPath.nil
  | cons p q hp hq hdis ih =>
    apply (simple_walk_append_of_disjoint_initial_support p q.toWalk hp ih ?_).1
    intro x hx hmem
    rcases (mem_toWalk_support q x).mp hmem with hlast | hinitial
    · exact (hdis x hx).2 hlast
    · exact (hdis x hx).1 hinitial
end SimpleWalkChain
end Oberwolfach
