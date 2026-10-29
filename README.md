# Navier–Stokes — enunciado formal em Lean 4 / Mathlib

Este repositório contém **o enunciado** do problema como uma proposição de Lean (`Prop`),
construída só com definições do Mathlib. **Não é uma solução**: o problema continua aberto
(`OPEN_MATH = true`).

- Enunciado: [`ClayNavierStokes/Statement.lean`](ClayNavierStokes/Statement.lean)
- Fonte do texto oficial: C. Fefferman, *Existence and smoothness of the Navier–Stokes equation* (descrição oficial do Clay Mathematics Institute)
- Mathlib: commit `8fe7ce475b056f0b266d7107893f2c4d772c712f` (28/10/2026), Lean `v4.36.0-rc2`
- Sem `axiom`, `sorry`, `native_decide`, marcadores (`:= True`) ou correspondências inventadas.

## Teste de não vacuidade (provado no kernel)

`zero_solves`: dado inicial nulo tem solução nula, então o sistema não é contraditório. `A_or_C`: `A ν ∨ C ν` é provável só com lógica clássica, então o prêmio não é a disjunção, e sim uma prova de uma das afirmações (A), (B), (C) ou (D).

## Axiomas (`#print axioms`, saída real)

| Declaração | Axiomas |
|---|---|
| `ClayNavierStokes.ClayA` | `[propext, Classical.choice, Quot.sound]` |
| `ClayNavierStokes.ClayB` | `[propext, Classical.choice, Quot.sound]` |
| `ClayNavierStokes.ClayC` | `[propext, Classical.choice, Quot.sound]` |
| `ClayNavierStokes.ClayD` | `[propext, Classical.choice, Quot.sound]` |
| `ClayNavierStokes.zero_solves` | `[propext, Classical.choice, Quot.sound]` |
| `ClayNavierStokes.A_or_C` | `[propext, Classical.choice, Quot.sound]` |

`Classical.choice` vem do Mathlib, não deste arquivo: o próprio tipo `ℝ` já depende dele (`#print axioms Real` → `[propext, Classical.choice, Quot.sound]`), e o mesmo vale para `ℂ`, `Polynomial ℕ` e a máquina `TM2`. São os três axiomas padrão do Lean; nenhum axioma deste repositório aparece.

[`ClayNavierStokes/Audit.lean`](ClayNavierStokes/Audit.lean) fixa essas listas com `#guard_msgs`, e o CI roda
`lake build`: se surgir um axioma novo (ou `sorryAx`), a compilação falha.

## Compilar

```
lake exe cache get
lake build
```
