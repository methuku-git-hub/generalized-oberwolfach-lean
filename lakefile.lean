import Lake
open Lake DSL
package oberwolfachVerification
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"
@[default_target]
lean_lib Oberwolfach

lean_lib FixedPointTheorems

lean_lib HadwigerLean

lean_lib Challenge

lean_lib Solution
