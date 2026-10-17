import ProductExpansion

/-!
# Axiom check

Run `lake env lean Verify.lean` after `lake build`. Each `#guard_msgs` fails unless the theorem
depends only on the three standard axioms of Lean and Mathlib (`propext`, `Classical.choice`,
`Quot.sound`); in particular, no `sorry` (`sorryAx`) and no new axioms are used.
-/

/-- info: 'ProductExpansion.paperTheorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProductExpansion.paperTheorem

/--
info: 'ProductExpansion.mainTheoremUniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProductExpansion.mainTheoremUniform

/-- info: 'ProductExpansion.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProductExpansion.mainTheorem
