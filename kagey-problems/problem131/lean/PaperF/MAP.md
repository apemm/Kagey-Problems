# Paper F: map from the paper to the Lean proofs

Paper F is `paperF/problem131_levy.tex`, the lattice Lévy walk with two run laws. This
library formalizes the exact identities of Section 2 (`paperF/sec_setting.tex`, Sections 2.4
and 2.5). It also formalizes the algebraic part of Theorem `thm:inverse`(a)
(Section 7, `paperF/sec_inverse.tex`). The table cites statement labels, not numbers, since
the numbers change when statements move. Layout as of October 24, 2026.

The library is `PaperF`. It has the root `PaperF.lean` and 7 modules in `PaperF/`, all in
namespace `Kagey131.PaperF.Levy`. That namespace is separate from the older
`Kagey131.PaperF.FL1`, `Kagey131.PaperF.FL2` and `Kagey131.PaperF.Compose`, which live in
`PaperD` and belong to the heavy-tail and aging paper, now archived. The library builds against
Lean 4 v4.33.1 and Mathlib v4.33.1. No module uses `sorry` or `native_decide`.

| Module | Contents |
|---|---|
| `Basic` | model, words, weights, laws, generating polynomials, convolution, renewal function |
| `FirstRun` | scan unrolled to the end of a run, `prop:first-run`, the fresh start as a preparation |
| `FinalRun` | the recursion for `A_t` and `B_t`, `prop:final-run` |
| `Kernels` | renewal equation, `eq:kernel-sums`, `prop:fresh-identity` and the fresh-minus identity |
| `Green` | `lem:green`, the tail-sum formula for the mean |
| `Counting` | `lem:counting`, first part |
| `Inverse` | renewal inversion for `thm:inverse`(a) |

## Model and conventions

- A sign is a `Bool`: `true` is plus and `false` is minus, and `!s` is the opposite sign.
- The run laws are one function `f : Bool → ℕ → ℝ`, where `f s n` is the mass of a run of sign
  `s` and length `n`. The mass functions are real-valued functions on `ℕ`. Where positive run
  lengths matter, the hypothesis `h0 : ∀ s, f s 0 = 0` is assumed. Total mass one and
  nonnegativity are assumed only where named in the table. Most identities hold without them.
- The survival function is the finite expression `T f s n = 1 - ∑_{m<n} f s m` for `n ≥ 1`, with
  `T f s 0 = 0`, as the paper extends `T` by zero. If `f s` sums to one, then
  `T f s n = ∑_{m ≥ n} f s m` for `n ≥ 1` (`hasSum_T`).
- A walk of `N` slots is a word `w : Fin N → Bool`. Under a fresh start of sign `σ`, the weight
  `weight f σ` of a word is the product of `f` over its runs, except that the last run
  contributes `T` of its length. A word whose first letter is not `σ` has weight `0`. The law
  `law f σ N k` is the total weight of the words with `N` slots and `k` plus slots. Each word is
  a composition of `N` into alternating runs, so the law is the sum over compositions with the
  last run censored by `T`. So `F^σ_N(k) = law f σ N k`. Here `P_N(0)` for `N = 0` is `1`.
- A preparation is `ν : Bool → ℕ → ℝ` with `ν s d = Prob(Σ = s, D = d)`. Its tail is
  `prepTail ν s n = ∑'_{d ≥ n} ν s d`, which is `Q_s(n)`. `prepLaw f ν N k` is the total
  weight in which the first run has mass `ν` and is censored by `prepTail ν`. Only `d ≥ 1`
  enters, so `ν s 0` plays no role. `prepLaw_fresh` shows that the fresh preparation
  (`ν_{σ₀} = f_{σ₀}`, `ν_{!σ₀} = 0`) gives back `law f σ₀` when `f σ₀` sums to one.
- Kernels: `uK f s m = f_s^{*m}` with `uK f s 0 = δ_0` (via `convPow`). The other kernel is
  `qK f s m = T_s * u^s_{m-1}`, used for `m ≥ 1`. The renewal function is
  `renewal (f s) j = ∑'_{m ≥ 0} f_s^{*m}(j)`, which is a finite sum over `m ≤ j` when `f s 0 = 0`
  (`renewal_eq_sum`). It has `u(0) = 1`, as in the paper.
- The proofs work in the ring `ℝ[Y]⟦X⟧`, where `X` counts slots and `Y` counts plus slots. The
  identities are derived there and then read off coefficientwise. The statements themselves are
  finite sums of real numbers, except for the `HasSum` statements of `lem:green` and the
  tail-sum formula.

### The recursion for `A_t` and `B_t`

The paper states this recursion in Section `sec:verify` as `eq:run-recursion`, with
`a_t, b_t` for `A_t, B_t`, together with the run form `eq:run-sum` of `prop:final-run`, which is
the form that `final_run` proves. Proposition `prop:final-run` itself is stated in the explicit
form `eq:final-explicit`, which equals `eq:run-sum` by `eq:rho-rep`. The Lean
definition `AB` (with `A f t k = AB f t true k` and `B f t k = AB f t false k`) uses the
following recursion. It starts from `A_0 = δ_0` and `B_0 = 0` (a fresh plus start):

- `B_s(k) = ∑_{t<s, s-t ≤ k} A_t(k-(s-t)) f_+(s-t)` (a plus run of length `l = s-t` starting at
  slot `t+1` sends `A_t(k)` to `B_{t+l}(k+l)` with weight `f_+(l)`), and
- `A_s(k) = ∑_{t<s} B_t(k) f_-(s-t)` for `s ≥ 1` (a minus run of length `l` sends `B_t(k)` to
  `A_{t+l}(k)` with weight `f_-(l)`).

These are `B_succ` and `A_succ`. `AB_eq_zero_of_lt` gives `A_t(k) = B_t(k) = 0` for `k > t`.

## Table

The hypotheses use the names `h0 : ∀ s, f s 0 = 0`, `h1 : HasSum (f s) 1` and
`hμ : HasSum (T f s) μ`. All axioms listed were printed with `#print axioms` in a scratch file
importing `PaperF`.

| Paper label | Statement | Lean declaration (module) | Hypotheses | Axioms |
|---|---|---|---|---|
| `prop:final-run` | `P_N(N-j) = ∑_{t=j}^{N-1} A_t(t-j) T_+(N-t) + ∑_{m=1}^{j} B_{N-m}(N-j) T_-(m)` for a fresh plus start | `final_run` (`FinalRun`) | `h0`, `1 ≤ N`, `j ≤ N` | propext, Classical.choice, Quot.sound |
| `prop:final-run`, recursion | `A_s`, `B_s` as above; vanishing for `k > t` | `A_zero`, `B_zero`, `A_succ`, `B_succ`, `AB_eq_zero_of_lt` (`FinalRun`) | none | propext, Classical.choice, Quot.sound |
| `prop:final-run`, series form | `lawS f true - 1 = A(X,Y) T_+(XY) + B(X,Y) T_-(X)` | `lawS_true_eq_final` (`FinalRun`) | `h0` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity` | `F^+_N(k) = ∑_{m=1}^{M} [u^-_m(l) q^+_{m+1}(k) + u^+_m(k) q^-_m(l)]`, `k + l = N` | `fresh_plus` (`Kernels`) | `h0`, `1 ≤ k`, `1 ≤ l`, `k ≤ M` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity` | `F^+_N(N) = T_+(N)` | `fresh_plus_full` (`Kernels`) | `h0`, `1 ≤ N` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity` | `F^+_N(0) = 0` | `law_true_zero` (`Basic`) | `1 ≤ N` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity`, minus | `F^-_N(k) = ∑_{m=1}^{M} [u^+_m(k) q^-_{m+1}(l) + u^-_m(l) q^+_m(k)]` | `fresh_minus` (`Kernels`) | `h0`, `1 ≤ k`, `1 ≤ l`, `k ≤ M` | propext, Classical.choice, Quot.sound |
| `prop:fresh-identity`, minus | `F^-_N(0) = T_-(N)`, `F^-_N(N) = 0` | `fresh_minus_empty` (`Green`), `law_false_full` (`Basic`) | `h0`, `1 ≤ N` (resp. `1 ≤ N`) | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums` | `∑_{m=1}^{M} u_m(k) = u(k)` | `kernel_sum_u` (`Kernels`) | `f s 0 = 0`, `1 ≤ k ≤ M` | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums` | `∑_{m=1}^{M} q_m(k) = 1` | `kernel_sum_q` (`Kernels`) | `f s 0 = 0`, `1 ≤ k ≤ M` | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums` | `∑_{m=1}^{M} q_{m+1}(k) = 1 - T(k)` | `kernel_sum_q_succ` (`Kernels`) | `f s 0 = 0`, `1 ≤ k ≤ M` | propext, Classical.choice, Quot.sound |
| `eq:kernel-sums`, finiteness | `u_m(k) = q_m(k) = 0` for `k < m` | `uK_eq_zero_of_lt`, `qK_eq_zero_of_lt` (`Kernels`) | `f s 0 = 0` | propext, Classical.choice, Quot.sound |
| `sec:kernels`, `u_σ` | renewal equation `u = δ_0 + f * u`; `u` as a finite sum | `renewal_eq`, `renewal_eq_pointwise` (`Kernels`), `renewal_eq_sum` (`Basic`) | `f s 0 = 0` | propext, Classical.choice, Quot.sound |
| `prop:first-run` | `P_N(k) = Q_+(N)1{k=N} + Q_-(N)1{k=0} + ∑_{1≤d<N} ν_+(d) F^-_{N-d}(k-d) + ∑_{1≤d<N} ν_-(d) F^+_{N-d}(k)`; the `ν_+` term is `0` when `k < d` | `first_run` (`FirstRun`) | `1 ≤ N`; any `ν` | propext, Classical.choice, Quot.sound |
| `prop:first-run` | `P_N(N) = Q_+(N)`, `P_N(0) = Q_-(N)` | `first_run_full`, `first_run_empty` (`FirstRun`) | `1 ≤ N` | propext, Classical.choice, Quot.sound |
| `sec:runs`, fresh start | the fresh preparation gives the fresh law | `prepLaw_fresh` (`FirstRun`) | `HasSum (f σ₀) 1` | propext, Classical.choice, Quot.sound |
| `lem:green` | `∑_{m ≥ 0} Π^+_m(b) = 1 + μ_- u_+(b)` (as `HasSum`) | `green_plus` (`Green`) | `h0`, `HasSum (f false) 1`, `HasSum (T f false) μ`, `1 ≤ b` | propext, Classical.choice, Quot.sound |
| `lem:green` | `∑_{m ≥ 0} Π^-_m(b) = 1 + μ_+ u_-(b)` (as `HasSum`) | `green_minus` (`Green`) | `h0`, `HasSum (f true) 1`, `HasSum (T f true) μ`, `1 ≤ b` | propext, Classical.choice, Quot.sound |
| `lem:green`, with the mean | the same, with `μ = ∑_n n f(n)` | `green_plus_of_mean`, `green_minus_of_mean` (`Green`) | `h0`, `f ≥ 0` (opposite sign), `HasSum f 1`, `HasSum (n f(n)) μ`, `1 ≤ b` | propext, Classical.choice, Quot.sound |
| `eq:means` | tail-sum formula `∑_{n≥1} T(n) = ∑_n n f(n)` | `hasSum_T_of_mean` (`Green`) | `f s ≥ 0`, `HasSum (f s) 1`, `HasSum (n f(n)) μ` | propext, Classical.choice, Quot.sound |
| `sec:runs` | `T(n) = ∑_{m ≥ n} f(m)` | `hasSum_T` (`Basic`) | `HasSum (f s) 1`, `1 ≤ n` | propext, Classical.choice, Quot.sound |
| `lem:counting`, first part | `N` slots, `N - j` plus slots, `j < N`: exactly `j` minus slots, at most `j+1` plus runs, a plus run of length `r` with `N - j ≤ (j+1) r` | `counting` (`Counting`) | `w.length = N`, `w.count true = N - j`, `j < N` | propext, Quot.sound |
| `lem:counting`, run structure | `segs w` describes `w` | `rebuild_segs`, `length_segs`, `sum_segs` (`Counting`) | none | propext (`rebuild_segs`, `length_segs`); propext, Quot.sound (`sum_segs`) |
| `thm:inverse`(a), inversion | `u = δ_0 + f * u`, `f 0 = 0`: `u(0) = 1`, `f(j) = u(j) - ∑_{i=1}^{j-1} f(i) u(j-i)` | `renewal_zero_of_eq`, `renewal_inverse` (`Inverse`) | `f 0 = 0`, `1 ≤ j` | propext, Classical.choice, Quot.sound |
| `thm:inverse`(a), `u` determines `f` | same `u` gives same `f`; `renewal f = renewal g → f = g` | `renewal_determines`, `renewal_injective` (`Inverse`) | `f 0 = g 0 = 0` | propext, Classical.choice, Quot.sound |

Notes on the forms chosen:

- The sums over `m` in `prop:fresh-identity` and `eq:kernel-sums` are written in the paper as
  `∑_{m ≥ 1}`. In Lean they are sums over `1 ≤ m ≤ M` for any `M ≥ k`. All the terms with
  `m > k` vanish (`uK_eq_zero_of_lt`, `qK_eq_zero_of_lt`), so `M = N` gives the paper's sums.
- In `lem:green` the sum over `m` is infinite. It is stated as the convergence
  `HasSum (fun m => K f σ m b) (1 + μ * renewal (f σ) b)` of the series over `m ≥ 0`, with
  `K f true m b = F^+_m(b)` and `K f false m b = F^-_m(m-b)` (zero for `m < b`). The mean enters
  as `HasSum (T f (!σ)) μ`. By `hasSum_T_of_mean` this follows from
  `HasSum (fun n => n * f (!σ) n) μ` for a nonnegative law summing to one. The `_of_mean`
  versions take that form. Only the law of the opposite sign needs to sum to one. No
  regularity is used.
- `prop:first-run` sums over `1 ≤ d < N`, since a first run has length at least one.
- The counting lemma is stated for a `List Bool` (for a word use `List.ofFn w`).

## Not formalized

- The second part of `lem:counting`, the bound `(j+1)^2 T_+(L)^2` for two plus runs of length at
  least `L`.
- The limit statements of `thm:inverse`(a) (`P_N(N-j)/P_N(N) → u_-(j)`), the normalization
  at the minus end, and `thm:inverse`(b). Only the renewal inversion is formalized.
- The boundary kernels `eq:kappa`, the kernel `v_σ`, the stationary preparation, and the claim
  that the recursion computes `P_N` in `O(N^3)` operations.
- Every asymptotic statement of the paper (`lem:profile` and Sections 3 to 7), which needs the
  hypotheses (RV), (LR) and (SPAN).

## Building

As for the other libraries, we build in a Lake workspace outside OneDrive. The workspace is
`~/lean-work/paperF`, whose `lakefile.toml` has `lean_lib PaperF` with `srcDir` set to this
folder and shares the Mathlib packages of `~/lean-work/kagey131`. `lake build PaperF` builds the
8 modules in a few minutes once Mathlib is cached, with no errors and no warnings. In a
normal clone, `lake exe cache get` and `lake build PaperF` in the `lean` folder do the same.
