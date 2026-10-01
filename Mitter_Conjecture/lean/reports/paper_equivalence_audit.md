# Independent paper equivalence and Jacobi proof audit

Date: 2026-09-29. Scope: comparison of the supplied original TeX with the new tCON manuscript, and independent verification of the changed visible-entry proof. This report does not certify a Lean build or independently reprove the unchanged hidden-slope sections.

## Audited source snapshot

Original:

`/Users/rinithpina/Documents/Research/Mitter_Conjecture/rank2dim3_wong_journal_en.tex`

SHA-256:

`8f3212ce168f13572e442fe754915a1d07486abcfc9145f33a26cdb1a090d950`

Revised manuscript:

`/Users/rinithpina/Documents/Codex/2026-09-29/xian-z/outputs/wong_jacobi_2026-09-29/02_tcon_paper/wong_jacobi_tcon.tex`

SHA-256 at the time of this audit:

`af1f0e4e3fea2892d128a91aab44982e1ba39d62c0711b71830f38485dac9dcc`

Any subsequent typesetting or wording change changes the full-source hash. The mathematical checks below concern the displayed snapshot; the unchanged theorem and model blocks have their own hashes below.

## Verdict

The revised visible-entry proof is mathematically valid under exactly the same original assumptions. All checked commutator signs, factors of 2, coefficient-extraction factors, and constant shifts are correct. The separation of the former symbol argument into a preceding lemma is valid and introduces no circular use of the desired constancy theorem. The inference that the final word `Y` lies in `G = E ∩ U₂` is valid.

One minor editorial omission was reported to the parent: deleting the old coefficient expansion also deleted the definition of the notation `[D^α]P`, although this notation is still used by the pure-head lemma and normalized rigidity proof. Restoring its definition avoids ambiguity with a Lie bracket. This is a notation issue, not a mathematical gap.

For readability, the sentence giving `Y ∈ G` can explicitly mention that the degree-three Poisson bracket of the constant degree-two symbols of `L₀` and `X` is zero. The existing inference is already correct.

## Original hypotheses and conclusions are preserved

Direct source-block comparison shows the following statements are byte-identical between original and revised manuscripts:

- `thm:main`;
- `cor:rank-two-constancy`;
- `thm:w12-constant`;
- `thm:ocone`;
- `thm:top-coeff`;
- `thm:shi-yau-affine`;
- `cor:function-space`;
- `thm:sector-I-smooth`;
- `thm:remaining-visible`.

In particular, the main theorem still assumes globally smooth real drift and observations on real three-space, the actual filtering differential-operator model, finite-dimensionality of the actual generated real Lie algebra, homogeneous linear rank two, and absence of a polynomial multiplication operator of degree exactly two. Its conclusion is the constancy of the actual whole Wong matrix, not a statement conditional on unexplained slope identities.

The model blocks `eq:D-eta-L0` and `eq:estimation-algebra` are also byte-identical. Their equation signs and the inclusion of observation squares in eta are unchanged.

Hashes of the unchanged exact TeX blocks (from `\begin{...}` through the corresponding first `\end{...}`):

| Block | SHA-256 |
|---|---|
| `thm:main` | `a1c84fcb1c698466b94dc0099555209518affc9c8ef9ad1631b13ce8941f7e57` |
| `thm:w12-constant` | `f2752b3efbab5cec5babb447434a3f9782ae554025c581138a2e25f873e37e29` |
| `eq:D-eta-L0` | `74ff9731d78a844404068aadac974d148fb76d504eecde11c9b670894d061776` |
| `eq:estimation-algebra` | `8830615052fa2a5a501a9cd69f97c10b7ff445e4a34cedb262a985c1402d1673` |

The unchanged Lean `MainStatement.lean` reviewed separately has SHA-256 `e9f51310ade6a4539e43c3074a1b35ed35e34bd85946761d53c93183d842a5cc`. Its `mainClaim` represents precisely this quadratic-free main theorem. The manuscript's unconditional corollary continues to use the cited 2020 function-element theorem and is correctly excluded from the claimed independent Lean verification scope.

## Factoring out normalized visible-symbol rigidity

The new lemma has only the original hypotheses together with the contradiction normalization `b₁ = 0`, `b₂ = b ≠ 0`. It asserts that every genuine second-order Lie element has constant `D₂²` and `D₁D₂` coefficients.

Its proof is the old symbol argument, now placed before the constancy theorem:

1. Double commutators with the two admitted coordinate multipliers give actual function elements. Ocone plus quadratic freeness and rank two make their visible coefficients affine and independent of the hidden coordinate.
2. Bracketing with the actual first-order `H₀,H₁` preserves `G` and gives the displayed visible-symbol identities with the manuscript's Poisson sign convention.
3. The pure-direction lemma eliminates the two slopes of `a₂₂` and the first-coordinate slopes of `a₁₁,a₁₂`.
4. The remaining mixed slope generates the exact projected recurrence `q_(r+1) = b(λ ξ₁² + γ ξ₁ξ₂) ∂_(ξ₂)q_r`; its tracked coefficient is `2^r(bγ)^(r+1)`.
5. Finite-dimensionality bounds differential order and forces `γ = 0`.

Nothing here uses the eventual conclusion `b = 0`. Thus the lemma is a legitimate consequence under a contradiction assumption, not a circular appeal to the main theorem. The lemma is valid for either sign of nonzero `b`; the theorem subsequently normalizes to `b > 0`.

The projected Poisson-bracket identity is used only when both projected symbols are independent of the hidden coordinate; its hypotheses hold at the starting step and in the induction. The pure-direction quotient argument also has the required invariance: the pure coefficient depends only on its own coordinate, so differentiating a discarded momentum factor cannot leak into the retained term.

## Constant shifts and first-order verticality

The manuscript defines shifted generators

```text
H₀ = [L₀,D₁] - (b₂+k₃)/2,
H₁ = [L₀,D₂] - (-b₁+h₃)/2.
```

The removed terms are constant scalar multiplication operators and commute with every operator. Consequently every bracket in the new proof, and the words `X = [L₀,H₀]`, `Y = [L₀,X]`, agrees with the same expression formed from the unshifted generators used by the Lean source.

After normalization `w = bx₂+b₀`, `∂₁w = 0`. The principal vector fields of `H₀,H₁` are `w∂₂+u∂₃` and `-w∂₁+v∂₃`. Therefore

```text
σ₁(J₁₁) = k₁ ξ₃,
σ₁(J₁₂) = h₁ ξ₃ = k₂ ξ₃,
```

where `J₁₁ = [D₁,H₀]`, `J₁₂ = [D₁,H₁]`, and the equality `h₁=k₂` is the already-established Bianchi identity. These are degree-one symbols, allowed to vanish if the relevant coefficient is zero.

Thus both J operators commute exactly with multiplication by `x₁,x₂`. Their lower-order multiplication parts do not affect these commutators. Since `w` depends only on `x₂`, `[w,J₁₂] = 0` exactly.

## Independent derivation of the Jacobi identities

All signs below use `[P,Q]=PQ-QP` and the manuscript convention `[D₂,D₁]=w`, hence `[D₁,D₂]=-w`.

First, Jacobi gives

```text
[D₂,H₀] - [D₁,H₁] = [L₀,w] = bD₂.
```

Also `[H₀,w] = w ∂₂w + u ∂₃w = bw`. Therefore

```text
[D₂,J₁₁] - [D₁,J₁₂]
  = [D₁,[D₂,H₀]-[D₁,H₁]] + [[D₂,D₁],H₀]
  = [D₁,bD₂] + [w,H₀]
  = -bw - bw
  = -2bw.
```

This verifies both minus signs and the factor 2 in `eq:jacobi-first-obstruction`.

Next, `X=[L₀,H₀]` satisfies

```text
[X,x₁] = J₁₁,
[X,x₂] = [L₀,w]+[D₂,H₀] = J₁₂+2bD₂.
```

For the mixed head of `Y=[L₀,X]`, expand Jacobi without using eta:

```text
[[Y,x₁],x₂]
  = [L₀,[[X,x₁],x₂]] + [D₂,[X,x₁]] + [D₁,[X,x₂]]
  = [D₂,J₁₁]+[D₁,J₁₂]+2b[D₁,D₂]
  = [D₂,J₁₁]+[D₁,J₁₂]-2bw
  = 2[D₂,J₁₁].
```

The first term vanishes because `[J₁₁,x₂]=0`; the last step uses the first obstruction identity.

For the pure second-coordinate head,

```text
[[X,x₂],x₂] = 2b·1,
[[Y,x₂],x₂]
  = [L₀,2b·1]+2[D₂,J₁₂+2bD₂]
  = 2[D₂,J₁₂].
```

This verifies both factors in `eq:jacobi-head-extraction`.

## Why Y belongs to G, and extraction factors

`H₀` is an actual first-order Lie element with affine principal vector field. Since `L₀` has constant degree-two symbol `|ξ|²/2`, the degree-two symbol of `X=[L₀,H₀]` is constant. The commutator `Y=[L₀,X]` has order at most three a priori, but its degree-three symbol is the Poisson bracket of two constant-coefficient momentum polynomials and therefore vanishes. Hence `ord(Y)≤2`. All the words are actual Lie brackets of elements of E, so `Y∈E`, proving `Y∈G`.

This reasoning also covers the degenerate case `ord(X)<2`, for which the degree-two symbol is simply zero.

For a second-order D-normal form, `[[Y,x₁],x₂]` extracts exactly the coefficient of `D₁D₂`, while `[[Y,x₂],x₂]` extracts twice the coefficient of `D₂²`. Hidden-momentum terms give zero and lower-order terms vanish after two coordinate commutators. Therefore the normalized rigidity lemma proves that both heads are constant multiplication operators, and hence both `[D₂,J₁₁]` and `[D₂,J₁₂]` are constant multiplication operators. Division by 2 is valid over the real field.

## Final contradiction

Commuting the first obstruction identity with `D₂` yields a right-hand side

```text
[D₂,-2bw] = -2b[D₂,w] = -2b²·1.
```

On the left,

```text
[D₂,[D₁,J₁₂]]
  = [D₁,[D₂,J₁₂]] + [[D₂,D₁],J₁₂]
  = [D₁,[D₂,J₁₂]] + [w,J₁₂].
```

The second summand is zero by verticality. Both other brackets vanish because the inner operators are now constant multipliers. Hence the manuscript's final identity `0=-2b²·1` is correct. The identity operator on globally smooth real functions is nonzero (apply it to the constant-one function), and `b>0`, so the contradiction follows.

No derivative of eta has been expanded or compared in this final argument. The earlier symbol/order-growth rigidity is retained and remains necessary for the proof as written. The new remark describes this boundary accurately.

## Relation to the rest of the paper and the Lean statement

The full source diff shows that, outside typesetting/title/bibliography changes and the revised verification-scope appendix, the mathematical changes are confined to the visible-entry section and a corresponding abstract sentence. The hidden-slope sections and completion paragraph retain their original argument. Their input `b₁=b₂=0` is exactly the output of the rewritten theorem.

The Lean proof uses indices 0 and 1 for the manuscript's visible indices 1 and 2 and unshifted generators, as explained above. The same-signature actual-model replacement theorem takes the two constant heads of the actual `Y f h`; those heads are proved by the previous finite-dimensional symbol argument, rather than introduced as new assumptions of `mainClaim`. This agrees with the factored manuscript lemma and final theorem.

The verification appendix correctly limits its claims to the quadratic-free main proposition, the real Euler case needed by that proposition, and the actual differential-operator model. It does not claim a separate Lean certificate for the 2020 corollary, the broader complex Euler statement, or stochastic existence. Actual successful compilation and axiom status must be taken from the accompanying fresh verification report, not inferred from this mathematical audit.


## Typesetting verification update (2026-09-29)

The notation definition identified above has been restored. The subsequent changes are confined to template compatibility, fonts, author-year citations, APA-style bibliography, and an appendix page break. The mathematical formulas, theorem hypotheses and proof deductions were not changed by this typesetting pass.

Current typeset TeX SHA-256: `472f79ce4816c89ac4eee0485fde5b474bee55926e3b2fdf428d371b4da250f0`.

The preceding source-snapshot hash is retained as historical audit provenance; this new hash identifies the typeset source actually used for the visually checked 23-page PDF.

## Accepted-verification appendix update (2026-09-29)

A single paragraph was added to the verification appendix after acceptance passed. It records 123 source modules, 1,281 audited theorem declarations, zero sorry placeholders, only propext/Classical.choice/Quot.sound, and the audited Jacobi dependency route. It explicitly describes a baseline-assisted, dependency-checked incremental build and does not claim a full rebuild. No mathematical assumptions, statements, formulas or proof deductions changed. The affected final PDF page was recompiled and visually checked.

Final TeX SHA-256: `472f79ce4816c89ac4eee0485fde5b474bee55926e3b2fdf428d371b4da250f0`. Final PDF SHA-256: `33d00bf3be156aaa60bfe5cd792e6195d692200710ed5b2a1ccc8e8bbc3ee758`.
