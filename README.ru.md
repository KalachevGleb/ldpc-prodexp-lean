# Расширение произведения LDPC кодов: формализация в Lean 4

[![Lean Action CI](https://github.com/KalachevGleb/ldpc-prodexp-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/KalachevGleb/ldpc-prodexp-lean/actions/workflows/lean_action_ci.yml)

[English](README.md) | **Русский**

В репозитории находится полное формальное доказательство основной теоремы работы

> Г. В. Калачев. *Расширение произведения LDPC кодов*.
> Интеллектуальные системы. Теория и приложения, в печати.

на языке [Lean 4](https://lean-lang.org) с библиотекой
[Mathlib](https://github.com/leanprover-community/mathlib4).

Теорема утверждает, что расширение произведения любого фиксированного числа LDPC кодов, графы
Таннера которых являются вершинными экспандерами без потерь (lossless), ограничено снизу
положительной константой.

## Теорема

Пусть $`\mathcal C_1,\dots,\mathcal C_m\subseteq\mathbb F_q^n`$ — линейные коды. Код $`\mathcal C^{(i)}`$
состоит из слов $`x\colon[n]^m\to\mathbb F_q`$, у которых ограничение на каждую линию направления $`i`$
лежит в $`\mathcal C_i`$, и $`\mathcal C_1\boxplus\dots\boxplus\mathcal C_m:=\mathcal C^{(1)}+\dots+\mathcal C^{(m)}`$.
Для такого слова $`\lvert x\rvert`$ — вес Хэмминга, $`\lvert x\rvert_i`$ — число линий направления $`i`$,
на которых $`x`$ ненулевое. *Расширение произведения* —

```math
\rho(\mathcal C_1,\dots,\mathcal C_m):=\frac1n\min_{x\in\mathcal C_1\boxplus\dots\boxplus\mathcal C_m\setminus\{0\}}
\frac{\lvert x\rvert}{\lvert x\rvert_{\boxplus}},\qquad
\lvert x\rvert_{\boxplus}:=\min\Bigl\{\sum_i\lvert a_i\rvert_i\Bigm| x=\sum_i a_i,\ a_i\in\mathcal C^{(i)}\Bigr\}.
```

Двудольный граф с левыми степенями $`\delta`$ — $`(\alpha,\varepsilon)`$-экспандер, если у любого
множества $`S`$ левых вершин с $`\lvert S\rvert\le\alpha\lvert L\rvert`$ не меньше
$`(1-\varepsilon)\delta\lvert S\rvert`$ соседей. $`\mathsf{ExpLDPC}(\delta,\alpha,\varepsilon)`$ — класс
кодов $`\mathcal C=\ker H`$, где $`H`$ — матрица смежности бирегулярного $`(\alpha,\varepsilon)`$-экспандера
с левой степенью $`\delta`$ (левые вершины — столбцы $`H`$, т.е. позиции кода).

**Теорема 1.** Для любых $`m,\delta\ge1`$, $`R_1,\dots,R_m\in(0,1)`$, $`\alpha>0`$ и $`\varepsilon\in[0,1/16]`$
существует $`\rho_0>0`$, зависящее только от $`m`$, $`\alpha`$ и $`\Delta:=\lfloor\delta/(1-\max_iR_i)\rfloor`$,
такое, что $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge\rho_0`$ для любой длины $`n`$ и любых кодов
$`\mathcal C_i\in\mathsf{ExpLDPC}(\delta,\alpha,\varepsilon)`$ длины $`n`$ и скорости не больше $`R_i`$.

В Lean ([`ProductExpansion/Paper.lean`](ProductExpansion/Paper.lean),
[`ProductExpansion/Main.lean`](ProductExpansion/Main.lean)):

```lean
def PaperTheoremStatement : Prop :=
  ∃ ρ : ℕ → ℕ → ℝ → ℝ, (∀ m Δ α, 0 < α → 0 < ρ m Δ α) ∧
    ∀ (F : Type) [Field F] [DecidableEq F] (m δ : ℕ) (R : Fin m → ℝ) (Rmax α ε : ℝ),
      0 < δ → (∀ i, R i ≤ Rmax) → Rmax < 1 → 0 < α → 0 ≤ ε → ε ≤ 1 / 16 →
      ∀ (n : ℕ) (C : Fin m → Submodule F (Fin n → F)),
        (∀ i, InELDPC (C i) δ α ε) → (∀ i, (Module.finrank F (C i) : ℝ) ≤ R i * n) →
        prodExpanding C (ρ m ⌊(δ : ℝ) / (1 - Rmax)⌋₊ α)

theorem paperTheorem : PaperTheoremStatement
```

Одна функция `ρ m Δ α` выражает то, что константа зависит только от $`m`$, $`\Delta`$ и $`\alpha`$: она не
зависит от поля, длины $`n`$, левой степени $`\delta`$ и $`\varepsilon`$. Формальная формулировка немного
общее текстовой: поле `F` произвольно (конечное или нет), важен только носитель $`H`$ (ненулевые элементы
произвольны), `Rmax` — любая общая верхняя оценка скоростей.

Теорема выводится из варианта, в котором вместо скоростей ограничены правые степени, а регулярность
графов справа не требуется ([`ProductExpansion/MainLemma.lean`](ProductExpansion/MainLemma.lean)):

```lean
def MainTheoremUniformStatement : Prop :=
  ∀ (m Δ : ℕ) (α : ℝ), 0 < α → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (F : Type) [Field F] [DecidableEq F] (δ : ℕ) (ε : ℝ), 0 < δ → 0 ≤ ε → ε ≤ 1 / 16 →
    ∀ (n : ℕ) (P : Fin m → Type) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
      (H : ∀ i, Matrix (P i) (Fin n) F), (∀ i, IsExpanderMatrix (H i) δ Δ α ε) →
      prodExpanding (fun i => kerCode (H i)) ρ₀

theorem mainTheoremUniform : MainTheoremUniformStatement
```

## Что нужно проверить читателю

Доказательства проверяет Lean. Чтобы доверять результату, достаточно убедиться, что определения
в формулировках означают то же, что в тезисах. Это около 200 строк:
[`Basic.lean`](ProductExpansion/Basic.lean), определения `IsBiregular`, `InELDPC` и
`PaperTheoremStatement` в [`Paper.lean`](ProductExpansion/Paper.lean) и
`MainTheoremUniformStatement` в [`MainLemma.lean`](ProductExpansion/MainLemma.lean).

| Тезисы | Lean |
| --- | --- |
| поле $`\mathbb F_q`$ | любое поле `F` |
| слово на кубе $`[n]^m`$ | `(ι → Fin n) → F`, в теореме `ι = Fin m` |
| линия направления $`i`$ через $`y`$, ограничение $`x\vert_\ell`$ | `line i y`, `restrictLine x i y` |
| $`\mathcal C^{(i)}`$ | `colCode C i` |
| $`\mathcal C_1\boxplus\dots\boxplus\mathcal C_m`$ | `boxplus C` |
| $`\lvert x\rvert`$, $`\lvert x\rvert_i`$ | `weight x`, `lineWeight x i _` |
| $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge\rho_0`$ | `prodExpanding C ρ₀` |
| окрестность $`N(S)`$ в графе Таннера $`H`$ | `nbhd H S` |
| $`\ker H`$ | `kerCode H` |
| $`(\alpha,\varepsilon)`$-экспандер с левой степенью $`\delta`$ и правыми $`\le\Delta`$ | `IsExpanderMatrix H δ Δ α ε` |
| $`\mathcal C\in\mathsf{ExpLDPC}(\delta,\alpha,\varepsilon)`$ | `InELDPC C δ α ε` |
| скорость $`\mathcal C`$ не больше $`R`$ | `Module.finrank F C ≤ R * n` |

`prodExpanding C ρ₀` означает, что у каждого $`x\in\mathcal C_1\boxplus\dots\boxplus\mathcal C_m`$ есть
разложение $`x=\sum_i a_i`$, $`a_i\in\mathcal C^{(i)}`$, с $`\rho_0\,n\sum_i\lvert a_i\rvert_i\le\lvert x\rvert`$;
это равносильно $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge\rho_0`$.

Файл [`Verify.lean`](Verify.lean) проверяет, что теоремы используют только стандартные аксиомы
`propext`, `Classical.choice` и `Quot.sound`; в частности, `sorry` нет.

## Сборка

Установите Lean через [elan](https://github.com/leanprover/elan) (версия задана в `lean-toolchain`:
Lean 4.34.1, Mathlib v4.34.1), затем

```sh
git clone https://github.com/KalachevGleb/ldpc-prodexp-lean.git
cd ldpc-prodexp-lean
lake exe cache get        # готовые .olean Mathlib
lake build                # проверка всех доказательств
lake env lean Verify.lean # проверка аксиом; при успехе ничего не выводит
```

После загрузки кэша Mathlib `lake build` занимает около 3 минут.

Те же шаги выполняются в GitHub Actions при каждом push
([`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)).

## Устройство доказательства

| Модуль | Содержание |
| --- | --- |
| `Basic` | Куб, линии, $`\mathcal C^{(i)}`$, $`\boxplus`$, веса, расширение произведения, матрицы-экспандеры. |
| `Expander` | Уникальные соседи, расстояние $`>\alpha n`$, жадное замыкание $`F_\theta`$ (леммы `gen-unique`, `gen-find`). |
| `Cube`, `CubeLemmas` | Грани, базы $`B_I`$, множества $`Y_I`$, замкнутые множества и их свойства (F1)–(F3), $`L(M)`$. |
| `Closure`, `Reduction` | Малые замкнутые надмножества (`gen-closure`), сведение расширения произведения к $`\mathrm P(m)`$ (`gen-reduction`), случай $`\alpha n<2`$. |
| `Syndrome`, `FaceSyn` | Синдромное условие $`\mathrm S(E)`$ (`def:syn`), лемма о синдроме грани (`face-syn`). |
| `Canonical` | Канонические множества ошибок (`def:can`), лемма `CL`, хорошие линии (`good`). |
| `MainInterface`, `Step2` … `Step5` | Формулировки и доказательства шагов 2–5 леммы $`\mathrm D(d)`$. |
| `MainLemma` | Константы $`\kappa_d`$, лемма $`\mathrm D(d)`$ индукцией, следствие $`\mathrm P(d)`$, теорема 1 для наборов матриц-экспандеров. |
| `Paper`, `Main` | Оценка правых степеней через скорость; итоговые теоремы. |

Комментарии в коде ссылаются на утверждения доказательства по коротким меткам:

| Метка | Утверждение |
| --- | --- |
| `gen-unique` | Если $`\lvert S\rvert\le\alpha n`$, то у $`S`$ не меньше $`(1-2\varepsilon)\delta\lvert S\rvert`$ уникальных соседей; расстояние $`\ker H`$ больше $`\alpha n`$. |
| `gen-find` | Оценки жадного замыкания $`F_\theta(R)`$: его мощность и $`\operatorname{supp}e\subseteq F_h(R)`$ при $`\operatorname{supp}(He)\subseteq R`$, $`h=(1-2\varepsilon)\delta`$. |
| `gen-closure` | Наименьшее $`\eta`$-замкнутое надмножество $`S\subseteq[n]^m`$ имеет мощность не больше $`((2^m+1)/\eta)^m\lvert S\rvert`$ (Калачев–Пантелеев, FOCS 2025, лемма 18). |
| `gen-reduction` | Если верно $`\mathrm P(m)`$ с порогом $`\eta`$, то $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge1/(m\,c_{m,\eta})`$. |
| `P(d)` | Всякое собственное $`\eta`$-замкнутое множество $`M\subseteq[n]^d`$, $`\eta\le\eta_d`$, порождается изнутри: каждое слово $`\mathcal C_1\boxplus\dots\boxplus\mathcal C_d`$ с носителем в $`M`$ есть сумма кодовых слов на линиях, лежащих в $`M`$. |
| `def:syn` | Синдромное условие $`\mathrm S_d(E)`$ с дефектом $`E`$. |
| `face-syn` | Ограничение слова, удовлетворяющего $`\mathrm S_d(E)`$, на грань удовлетворяет синдромному условию с явно заданным дефектом. |
| `def:can` | Канонические множества ошибок $`\mathrm{Bad}_J`$, $`\mathrm{Can}(Y)`$, $`\widehat Y`$. |
| `CL` | Замкнутость и согласованность канонических множеств. |
| `good` | Существование хорошей линии и её свойства (G1)–(G4). |
| `D(d)` | Декодирование с дефектом, основная лемма; доказывается индукцией по $`d`$ в пять шагов. |

Без ограничения общности в доказательстве $`\alpha\le1`$ и $`\varepsilon=1/16`$, так как свойство расширения монотонно по этим параметрам.

## Об использовании инструментов ИИ

Формализация доказательства в системе Lean 4 выполнена с помощью модели Claude Opus 5.5 (Anthropic) в среде Claude Code.

## Цитирование и лицензия

При использовании кода ссылайтесь на работу, указанную выше (см. также [`CITATION.cff`](CITATION.cff)).
Код распространяется по лицензии Apache 2.0 ([`LICENSE`](LICENSE)), как и Mathlib.
