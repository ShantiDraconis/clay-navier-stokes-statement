import ClayNavierStokes.Statement

/-!
# Auditoria de axiomas

Cada `#guard_msgs` fixa a saída de `#print axioms`. Se aparecer qualquer axioma diferente
(inclusive `sorryAx`), a compilação falha.

`Classical.choice`, quando aparece, vem do Mathlib: `#print axioms Real` já dá
`[propext, Classical.choice, Quot.sound]` (idem `ℂ`, `Polynomial ℕ`, `Turing.TM2`).
-/

/-- info: 'ClayNavierStokes.ClayA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokes.ClayA

/-- info: 'ClayNavierStokes.ClayB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokes.ClayB

/-- info: 'ClayNavierStokes.ClayC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokes.ClayC

/-- info: 'ClayNavierStokes.ClayD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokes.ClayD

/-- info: 'ClayNavierStokes.zero_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokes.zero_solves

/-- info: 'ClayNavierStokes.A_or_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayNavierStokes.A_or_C
