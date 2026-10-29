import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Navier–Stokes — enunciado limpo

Fonte do enunciado: C. Fefferman, *Existence and smoothness of the Navier–Stokes equation*
(descrição oficial do Clay Mathematics Institute). Numeração das equações como no texto:

* (1) `∂ₜu + (u·∇)u = ν Δu − ∇p + f`
* (2) `div u = 0`
* (3) `u(x,0) = u⁰(x)`
* (4) `|∂ₓ^α u⁰(x)| ≤ C_{αK} (1+|x|)^{-K}`
* (5) `|∂ₓ^α ∂ₜ^m f(x,t)| ≤ C_{αmK} (1+|x|+t)^{-K}` em `ℝ³ × [0,∞)`
* (6) `p, u ∈ C^∞(ℝ³ × [0,∞))`
* (7) `∫ |u(x,t)|² dx < C` para todo `t ≥ 0`
* (8) `u⁰` e `f` periódicos de período 1 em cada coordenada
* (9) `|∂ₓ^α ∂ₜ^m f(x,t)| ≤ C_{αmK} (1+|t|)^{-K}` em `ℝ³ × [0,∞)`
* (10) `u(x,t)` periódico de período 1 em cada coordenada
* (11) `p, u ∈ C^∞(ℝ³ × [0,∞))`

O Clay paga por uma prova de qualquer UMA das afirmações (A), (B), (C), (D).

Escolhas de formalização (todas equivalentes ao texto):
* as derivadas são derivadas de Fréchet DENTRO do semiespaço fechado `H = ℝ³ × [0,∞)`
  (`fderivWithin`), que é convexo com interior não vazio, então as derivadas na borda `t = 0`
  são as laterais e estão bem definidas;
* as estimativas (4), (5), (9) usam a norma da derivada iterada `D^k`, que controla todas as
  derivadas parciais de ordem `k` e é controlada por elas (dimensão finita);
* a energia (7) usa a integral de Lebesgue em `[0,∞]`, para que "finita" não dependa de
  convenções de integrabilidade.

Sem axiomas, `sorry` ou marcadores. `OPEN_MATH = true` para (A), (B), (C), (D).
-/

namespace ClayNavierStokes

open scoped ContDiff
open MeasureTheory

/-- `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- O semiespaço fechado `ℝ³ × [0,∞)`, com coordenadas `(x, t)`. -/
def H : Set (E3 × ℝ) := Set.univ ×ˢ Set.Ici 0

/-- Vetor da base canônica `e_j`. -/
noncomputable def e (j : Fin 3) : E3 := EuclideanSpace.single j 1

section Operators

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `∂/∂x_j` dentro de `H`. -/
noncomputable def dx (j : Fin 3) (g : E3 × ℝ → F) (z : E3 × ℝ) : F :=
  fderivWithin ℝ g H z (e j, 0)

/-- `∂/∂t` dentro de `H`. -/
noncomputable def dt (g : E3 × ℝ → F) (z : E3 × ℝ) : F :=
  fderivWithin ℝ g H z (0, 1)

/-- Laplaciano espacial `Δg = ∑ⱼ ∂²g/∂x_j²`. -/
noncomputable def lap (g : E3 × ℝ → F) (z : E3 × ℝ) : F :=
  ∑ j, dx j (dx j g) z

@[simp] theorem dx_zero (j : Fin 3) : dx j (0 : E3 × ℝ → F) = 0 := by
  funext z; simp [dx]

end Operators

/-- Termo convectivo `(u·∇)u = ∑ⱼ u_j ∂u/∂x_j`. -/
noncomputable def convect (u : E3 × ℝ → E3) (z : E3 × ℝ) : E3 :=
  ∑ j, u z j • dx j u z

/-- Gradiente espacial da pressão `∇p = ∑ᵢ (∂p/∂x_i) e_i`. -/
noncomputable def grad (p : E3 × ℝ → ℝ) (z : E3 × ℝ) : E3 :=
  ∑ i, dx i p z • e i

/-- Divergência espacial `div u = ∑ⱼ ∂u_j/∂x_j`. -/
noncomputable def divx (u : E3 × ℝ → E3) (z : E3 × ℝ) : ℝ :=
  ∑ j, dx j u z j

/-! ## Hipóteses sobre os dados -/

/-- `u⁰` é lisa e tem divergência nula. -/
def SmoothDivFree (u0 : E3 → E3) : Prop :=
  ContDiff ℝ ∞ u0 ∧ ∀ x, ∑ j, fderiv ℝ u0 x (e j) j = 0

/-- (4): todas as derivadas de `u⁰` decaem mais rápido que qualquer potência de `|x|`. -/
def Decay4 (u0 : E3 → E3) : Prop :=
  ∀ k K : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ k u0 x‖ ≤ C

/-- (5): `f` lisa em `H` com todas as derivadas (em `x` e `t`) decaindo em `1 + |x| + t`. -/
def Forcing5 (f : E3 × ℝ → E3) : Prop :=
  ContDiffOn ℝ ∞ f H ∧
    ∀ k K : ℕ, ∃ C : ℝ, ∀ z ∈ H, (1 + ‖z.1‖ + z.2) ^ K * ‖iteratedFDerivWithin ℝ k f H z‖ ≤ C

/-- (8) para `u⁰`. -/
def Periodic0 (u0 : E3 → E3) : Prop :=
  ∀ j x, u0 (x + e j) = u0 x

/-- (8) para `f`. -/
def PeriodicF (f : E3 × ℝ → E3) : Prop :=
  ∀ j x t, 0 ≤ t → f (x + e j, t) = f (x, t)

/-- (9): `f` lisa em `H` com todas as derivadas decaindo em `1 + |t|`. -/
def Forcing9 (f : E3 × ℝ → E3) : Prop :=
  ContDiffOn ℝ ∞ f H ∧
    ∀ k K : ℕ, ∃ C : ℝ, ∀ z ∈ H, (1 + |z.2|) ^ K * ‖iteratedFDerivWithin ℝ k f H z‖ ≤ C

/-! ## Soluções -/

/-- (1), (2), (3) em `ℝ³ × [0,∞)`. -/
structure SolvesNS (ν : ℝ) (u0 : E3 → E3) (f : E3 × ℝ → E3)
    (p : E3 × ℝ → ℝ) (u : E3 × ℝ → E3) : Prop where
  /-- (1) -/
  momentum : ∀ z ∈ H, dt u z + convect u z = ν • lap u z - grad p z + f z
  /-- (2) -/
  incompressible : ∀ z ∈ H, divx u z = 0
  /-- (3) -/
  initial : ∀ x, u (x, 0) = u0 x

/-- (6) / (11): `p, u ∈ C^∞(ℝ³ × [0,∞))`. -/
def SmoothOnH (p : E3 × ℝ → ℝ) (u : E3 × ℝ → E3) : Prop :=
  ContDiffOn ℝ ∞ p H ∧ ContDiffOn ℝ ∞ u H

/-- (7): energia limitada uniformemente em `t ≥ 0`. -/
def BoundedEnergy (u : E3 × ℝ → E3) : Prop :=
  ∃ C : ℝ, ∀ t, 0 ≤ t → ∫⁻ x, ENNReal.ofReal (‖u (x, t)‖ ^ 2) ≤ ENNReal.ofReal C

/-- (10): `u` periódica de período 1 em cada coordenada espacial, em `ℝ³ × [0,∞)`. -/
def PeriodicSol (u : E3 × ℝ → E3) : Prop :=
  ∀ j x t, 0 ≤ t → u (x + e j, t) = u (x, t)

/-- Solução em `ℝ³`: (1), (2), (3), (6), (7). -/
def GoodSolutionR3 (ν : ℝ) (u0 : E3 → E3) (f : E3 × ℝ → E3)
    (p : E3 × ℝ → ℝ) (u : E3 × ℝ → E3) : Prop :=
  SolvesNS ν u0 f p u ∧ SmoothOnH p u ∧ BoundedEnergy u

/-- Solução em `ℝ³/ℤ³`: (1), (2), (3), (10), (11). -/
def GoodSolutionPer (ν : ℝ) (u0 : E3 → E3) (f : E3 × ℝ → E3)
    (p : E3 × ℝ → ℝ) (u : E3 × ℝ → E3) : Prop :=
  SolvesNS ν u0 f p u ∧ PeriodicSol u ∧ SmoothOnH p u

/-! ## As quatro afirmações do Clay, para viscosidade `ν` -/

/-- (A) Existência e suavidade em `ℝ³` (com `f ≡ 0`). -/
def A (ν : ℝ) : Prop :=
  ∀ u0, SmoothDivFree u0 → Decay4 u0 → ∃ p u, GoodSolutionR3 ν u0 0 p u

/-- (B) Existência e suavidade em `ℝ³/ℤ³` (com `f ≡ 0`). -/
def B (ν : ℝ) : Prop :=
  ∀ u0, SmoothDivFree u0 → Periodic0 u0 → ∃ p u, GoodSolutionPer ν u0 0 p u

/-- (C) Quebra em `ℝ³`. -/
def C (ν : ℝ) : Prop :=
  ∃ u0 f, SmoothDivFree u0 ∧ Decay4 u0 ∧ Forcing5 f ∧ ¬ ∃ p u, GoodSolutionR3 ν u0 f p u

/-- (D) Quebra em `ℝ³/ℤ³`. -/
def D (ν : ℝ) : Prop :=
  ∃ u0 f, SmoothDivFree u0 ∧ Periodic0 u0 ∧ PeriodicF f ∧ Forcing9 f ∧
    ¬ ∃ p u, GoodSolutionPer ν u0 f p u

/-- Os quatro problemas do Clay (texto: "Take ν > 0"). Por mudança de escala
`u ↦ u(x, t/ν)/ν`, valer para um `ν > 0` equivale a valer para todos. -/
def ClayA : Prop := ∀ ν > 0, A ν
def ClayB : Prop := ∀ ν > 0, B ν
def ClayC : Prop := ∀ ν > 0, C ν
def ClayD : Prop := ∀ ν > 0, D ν

/-! ## Testes de não vacuidade -/

theorem forcing5_zero : Forcing5 0 :=
  ⟨contDiffOn_const, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩

/-- Dado nulo tem solução nula: o sistema não é contraditório. -/
theorem zero_solves (ν : ℝ) : GoodSolutionR3 ν 0 0 0 0 := by
  refine ⟨⟨fun z _ => ?_, fun z _ => ?_, fun x => ?_⟩, ⟨contDiffOn_const, contDiffOn_const⟩,
    ⟨0, fun t _ => by simp⟩⟩
  · simp [dt, convect, lap, grad]
  · simp [divx]
  · rfl

/-- Por que o problema NÃO é a disjunção: `A ν ∨ C ν` é provável só com lógica clássica
(se (A) falha para algum `u⁰`, esse `u⁰` com `f ≡ 0` já é um exemplo de (C)). O prêmio exige uma
prova de uma das afirmações específicas, não da disjunção. -/
theorem A_or_C (ν : ℝ) : A ν ∨ C ν := by
  by_cases hA : A ν
  · exact Or.inl hA
  · right
    simp only [A, not_forall] at hA
    obtain ⟨u0, hdiv, hdec, hno⟩ := hA
    exact ⟨u0, 0, hdiv, hdec, forcing5_zero, hno⟩

end ClayNavierStokes
