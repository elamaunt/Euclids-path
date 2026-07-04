# 27. Product-core: lifting the trilemma, and the whole machine

<!--navtop-->
[← 26. Separating scale](26_SeparatingScale.md) · [Table of contents](00_Overview.md) · [28. MkNode →](28_MkNode.md)
<!--/navtop-->



> Source: `step00_product_core_rank_descent_corrected_ru_2026-07-01.md`. Lean:
> `Engine/ProductCore.lean` (`no_mismatch_core_eq`, `core_step_proved`,
> `coreCollision_of_infinite`, `product_core_engine_of_carrier` — without `sorry`; what
> remains open is exactly one structural input from the carrier).

In the previous chapter (§26) we closed `ProductHall` by pure arithmetic — the separating scale
$P_A > 6X_A+1$ made the reduction $a \mapsto a \bmod P_A$ injective on the legal layer. But when
this lever was carried over into the induction on genealogies (rank descent), three audit defects
resurrected the trilemma: extensionality of the passport, non-preservation of the bound $a < P_A$
at residual ranks, and non-finiteness of the signature space.

In this chapter we remove all three *with a single structural move* — by replacing the object of
induction. We stop inducting over genealogies with their absorber tail and pass to the pure
**product-core**, where extensionality becomes a genuine theorem rather than a hypothesis.

## Why the trilemma kept arising: fan-in inside the object

Recall the diagnosis of §26 (the audit's three objections to `no_mismatch_state_eq`):

1. **Extensionality.** For "no mismatch $\Rightarrow X_1 = X_2$" to hold, the passport must
   determine the state extensionally. But a genealogy-state carries a tail/absorber, and the
   boundary decomposition (BoundaryDecomp) yielded a $570 \to 1$ many-to-one map: distinct states
   with the same tail were merged. The passport had to be fine (for the lemma) and coarse (for the
   pigeonhole — the boxes principle, house name "pigeonhole", see the [glossary](GLOSSARY.md))
   at once — the same `UniqueLegalLift` trilemma, lifted one rank higher.
2. **The bound on the residual.** $a < P_A$ was proved only at top level; on descent to residual
   states it was not re-established.
3. **Finiteness of the signature.** The space of residues $(\mathbb{Z}/P_A)^r$ has size $P_A^r$,
   and as $A \to \infty$ (which the separating scale demands) it is unbounded, which kills the
   pigeonhole (which requires a fixed $A$).

An observation born of intuition: all three defects are *one and the same* defect, and it is
structural. The $570 \to 1$ fan-in lives in the state's tail. As long as the tail is part of the
induction object, it breaks extensionality (defect 1), drags along factors not covered by the
top-level bound (defect 2), and inflates the signature space (defect 3). It is natural to
conjecture: remove the tail from the object, and all three defects vanish at once. That is exactly
what we do.

## The object: a RankNode without a tail

We introduce the product-core node of rank $r$ — a side sign plus role-indexed factors, *without*
genealogy and without absorber.

**Definition 27.1** (product-core node). A node of rank $r$ is a pair of a side sign and a
role-indexed family of factors:

$$
\texttt{RankNode}\;r \;:=\; \bigl\{\, \mathrm{sign} : \texttt{Sign},\;\; \mathrm{factors} : \mathrm{Fin}\,r \to \mathbb{N} \,\bigr\}. \tag{27.1}
$$

In Lean this is `structure RankNode (r : ℕ)` with fields `sign : Sign` and `factors : Fin r → ℕ`,
where `Sign` is the two-element `inductive Sign | plus | minus`. The key phrase here is
`factors : Fin r → ℕ`: the state is **extensional** in the pair $(\mathrm{sign}, \mathrm{factors})$
by the very construction of the type. There is no tail in the record — because the $570 \to 1$
fan-in lived in the tail, and we did not put the tail into `RankNode`.

> **Note.** This is not cosmetic notation. Extensionality of a structure is what `funext` and
> injectivity of the constructor give for free for `RankNode`, and what could not in principle be
> obtained for a genealogy-state, where the tail glued distinct objects into one passport. We did
> not "declare" extensionality — we chose an object for which it holds.

## Fix 1: extensionality of the core — a genuine theorem

The first defect is removed head-on. If two product-core nodes agree in sign and in *all*
factors, they are equal.

**Theorem 27.2** (`no_mismatch_core_eq`). For $X_1, X_2 : \texttt{RankNode}\,r$, if
$X_1.\mathrm{sign} = X_2.\mathrm{sign}$ and $\forall k,\; X_1.\mathrm{factors}\,k = X_2.\mathrm{factors}\,k$,
then $X_1 = X_2$.

The proof is a constructor case split plus `funext`: `cases X₁; cases X₂`, then
`RankNode.mk.injEq` reduces the equality to a pair, and `⟨hsign, funext hfac⟩` closes it. What
this *means*: "no mismatched role $\Rightarrow$ the nodes are equal" is now a lemma, not an input
(in the house glossary an input/gate is a named unproven statement, see the [glossary](GLOSSARY.md)). The reason
why this works here and did not work in §31 is literally a single one: `RankNode` has no tail, so
pointwise equality of the factors is exactly the whole content of the state.

## Fix 2: AmbientLegal and the bound $a < P_A$ at all ranks

The second defect (non-preservation of the bound) is removed by a certificate that survives the
deletion of a role. We introduce a predicate.

**Definition 27.3** (`AmbientLegal`). A family of factors $\mathrm{factors} : \mathrm{Fin}\,r \to \mathbb{N}$
is *ambient-legal at scale* $X_A$ if there exists a common top legal side $N_0$ which all the
factors divide and which does not exceed the carrier bound:

$$
\texttt{AmbientLegal}\;X_A\;\mathrm{factors} \;:=\; \exists\, N_0 : \mathbb{N},\;\; 0 < N_0 \;\wedge\; N_0 \le 6X_A + 1 \;\wedge\; \forall i,\; \mathrm{factors}\,i \mid N_0. \tag{27.2}
$$

From this certificate the bound follows immediately.

**Theorem 27.4** (`ambient_factor_lt_primorial`). Under the separating scale $6X_A + 1 < P_A$ and
`AmbientLegal X_A factors` we have $\forall i,\; \mathrm{factors}\,i < P_A$.

Proof: $\mathrm{factors}\,i \mid N_0 \Rightarrow \mathrm{factors}\,i \le N_0$
(`Nat.le_of_dvd`), and $N_0 \le 6X_A+1 < P_A$; `omega` closes it. This is the same argument as in
§26 (`legal_lift_lt_primorial`), but now it is attached to a *family of roles* rather than to a
single factor.

Crucially, the certificate is preserved under role deletion. A residual is a subfamily of the
factors, so *the same* $N_0$ still serves.

**Theorem 27.5** (`ambientLegal_delete`). For $\mathrm{factors} : \mathrm{Fin}(r+1) \to \mathbb{N}$ and
a role $k$, `AmbientLegal X_A factors` implies
`AmbientLegal X_A (fun i => factors (k.succAbove i))`.

Here `Fin.succAbove` is the canonical embedding $\mathrm{Fin}\,r \hookrightarrow \mathrm{Fin}(r+1)$
skipping position $k$; the proof carries the same $N_0$ over to the subfamily. What this
*means*: the bound $a < P_A$ is now an **invariant of descent**, not a top-level fact. Defect 2
is closed structurally — deleting a role does not take us out of the legal layer.

## Fix 3: finiteness of the signature at fixed $A$

The third defect (non-finiteness of $(\mathbb{Z}/P_A)^r$) is removed by fixing $A$ *for the
duration of the pigeonhole* and taking the signature only with respect to the fixed $P_A$ and the
fixed $r$.

**Definition 27.6** (`CoreSig`). For fixed $P_A, r$, the core signature is a sign plus the residues of
the factors mod $P_A$, *without* genealogy:

$$
\texttt{CoreSig}\;P_A\;r \;:=\; \bigl\{\, \mathrm{sign} : \texttt{Sign},\;\; \mathrm{residues} : \mathrm{Fin}\,r \to \mathbb{Z}/P_A \,\bigr\}. \tag{27.3}
$$

**Theorem 27.7** (`coreSig_fintype`). Under $[\texttt{NeZero}\,P_A]$ (i.e. $P_A > 0$) and fixed
$r$, the type `CoreSig P_A r` is finite.

The instance is built via `Fintype.ofInjective` by the embedding
$s \mapsto (s.\mathrm{sign}, s.\mathrm{residues})$ into the finite type
$\texttt{Sign} \times (\mathrm{Fin}\,r \to \mathbb{Z}/P_A)$; injectivity is a constructor case
split. What this *means*: the signature space is finite, and the pigeonhole applies.

> **Note (on the tension between $A$ fixed and $A \to \infty$).** Defect 3 in §31 pointed to a
> direct contradiction: the separating scale wants $A \to \infty$, while the pigeonhole wants a
> fixed $A$. The resolution is honest, not illusory: the separating scale is used **inside a
> single layer $A$** (so that the reduction is injective and the bound holds), and the pigeonhole
> is applied *at that same fixed $A$* to the infinite family of starts within the layer. We do not
> send $A$ to infinity inside the pigeonhole — we work at a concrete $A$ for which the separating
> scale has already been reached (by §26 this happens already at $A \approx 50$, with a huge
> margin). The final infinitude of twins will come from the infinitude of layers from outside, not
> from inflating $r$ or $P_A$.

## The signature↔node bridge: ¬ProductHall on RankNode

Let us tie the node to its signature. `coreSigOf X := ⟨X.sign, fun i => (X.factors i : ZMod P_A)⟩`
is the node's passport. Now we transfer the argument of §26 to the product-core: equality of
residues plus the bound yields equality of factors.

**Theorem 27.8** (`no_productHall`). If at role $k$ both factors are $< P_A$ and congruent mod $P_A$,
yet $X_1.\mathrm{factors}\,k \ne X_2.\mathrm{factors}\,k$ — a contradiction ($\texttt{False}$).

Proof: for $a < P_A$ we have $\texttt{ZMod.val}(a \bmod P_A) = a$
(`ZMod.val_natCast` + `Nat.mod_eq_of_lt`); equality of residues then transfers to the $a$
themselves, and $\mathrm{hne}$ falls. From here — the final assembly "equal signatures + the bound
$\Rightarrow$ equal nodes".

**Theorem 27.9** (`factors_eq_of_coreSig`). If $\mathrm{coreSigOf}\,X_1 = \mathrm{coreSigOf}\,X_2$
and all factors of both are $< P_A$, then the factors coincide pointwise (by Theorem 27.8 (`no_productHall`),
arguing by contradiction).

**Theorem 27.10** (`rankNode_eq_of_coreSig`). Under the same hypotheses, $X_1 = X_2$: the sign is taken
from the signature (`congrArg CoreSig.sign`), the factors from the bound, and
Theorem 27.2 (`no_mismatch_core_eq`) assembles the node.

**Section takeaway.** The three fixes meet at one point: extensionality (Theorem 27.2, `no_mismatch_core_eq`)
gives sign-and-factors $\Rightarrow$ node; the bound (Theorem 27.4, `ambient_factor_lt_primorial`) gives
signature $\Rightarrow$ factors; finiteness will supply the existence of a collision. It remains
to run this as an induction.

## The base of the induction: rank 1 by arithmetic, without an external SNOL

Let us define the object of descent.

**Definition 27.11** (`CoreCollision`). $\texttt{CoreCollision}\;X_A\;P_A\;r$ is the existence of two
**distinct** ambient-legal RankNodes of rank $r$ with equal signature:

$$
\exists\, X_1\, X_2 : \texttt{RankNode}\,r,\;\; X_1 \ne X_2 \;\wedge\; \texttt{AmbientLegal}\,X_A\,X_1.\mathrm{factors} \;\wedge\; \texttt{AmbientLegal}\,X_A\,X_2.\mathrm{factors} \;\wedge\; \mathrm{coreSigOf}\,X_1 = \mathrm{coreSigOf}\,X_2. \tag{27.4}
$$

**Theorem 27.12** (`rank_one_coreCollision_absurd`). Under the separating scale $6X_A+1 < P_A$, a
collision of rank $1$ is impossible: $\texttt{CoreCollision}\,X_A\,P_A\,1 \Rightarrow \texttt{False}$.

The proof is entirely arithmetic: Theorem 27.4 (`ambient_factor_lt_primorial`) gives the bound for both,
Theorem 27.10 (`rankNode_eq_of_coreSig`) gives $X_1 = X_2$, contradicting $X_1 \ne X_2$. Let us stress: **the base
does not rely on an external SNOL** — it is closed by the same separating-scale arithmetic as the
induction step. This removes §31's dependence on a separate rank-1 SNOL module.

## The descent step $r \to r-1$: deleting the mismatched role

The defect of §31 was that the step `core_step` remained an *input* (a hypothesis). Here we
**prove** it. The instrument is role deletion.

**Definition 27.13** (`deleteFactor`). Deleting role $k$ from a $\texttt{RankNode}(r+1)$ yields a
$\texttt{RankNode}\,r$: the same sign, the factors re-indexed via `Fin.succAbove`.

**Theorem 27.14** (`delete_preserves_coreSig`). If the signatures of the full nodes are equal, then so
are the signatures after deleting the same role $k$ from both (the signs are the same; the
residues at the surviving roles are the same).

**Theorem 27.15** (`core_step_succ`). Under the separating scale, a collision of rank $r'+1$ yields a
collision of rank $r'$.

The logic of the step is the heart of the whole chapter, so let us go through it in detail. From
the equality of signatures and $X_1 \ne X_2$ there exists a mismatched role $k$ (otherwise
Theorem 27.2 (`no_mismatch_core_eq`) would give $X_1 = X_2$). We delete $k$, obtaining $Y_1, Y_2$. Their
signatures are equal (Theorem 27.14, `delete_preserves_coreSig`), the `AmbientLegal` certificates are preserved
(Theorem 27.5, `ambientLegal_delete`). Then comes the **residual dichotomy**:

- if $Y_1 \ne Y_2$, then $(Y_1, Y_2)$ is a collision of rank $r'$ (the descent has taken place);
- if $Y_1 = Y_2$, then the residual factors coincide and the entire mismatch is concentrated at
  role $k$: $X_1.\mathrm{factors}\,k \ne X_2.\mathrm{factors}\,k$, yet these factors are congruent
  mod $P_A$ and both are $< P_A$ — this is precisely a *ProductHall*, impossible by
  Theorem 27.8 (`no_productHall`). The branch is false.

In both branches we have either descended a rank or reached a contradiction. Hence the packaging:

**Theorem 27.16** (`core_step_proved`). Under the separating scale,
$\forall r,\; 2 \le r \Rightarrow \texttt{CoreCollision}\,X_A\,P_A\,r \Rightarrow \texttt{CoreCollision}\,X_A\,P_A\,(r-1)$
(from Theorem 27.15 (`core_step_succ`) by the substitution $r = (r-1)+1$).

> **Note.** Why does the trilemma not resurrect here? In §31 the step broke on the
> extensionality of the residual: deleting the tail could glue distinct states together. In
> `RankNode` there is no tail, so Theorem 27.2 (`no_mismatch_core_eq`, for the full node) and
> Theorem 27.14 (`delete_preserves_coreSig`, for the residual) both hold, while Theorem 27.8 (`no_productHall`) closes the
> degenerate branch without any appeal to the passport as a "normal form". Induction over the
> product-core **without a tail removes the fan-in from the object** — and with it the source of
> the trilemma.

## Assembling the induction: collision $\Rightarrow$ Engine

Recall: the Engine is the perpetual engine, the programme's central forbidden object
(see the [glossary](GLOSSARY.md)); anything that builds one is thereby false.

**Theorem 27.17** (`coreCollision_engine`). Under the separating scale and the step `core_step`
(now exhibited as Theorem 27.16 (`core_step_proved`)):
$\forall r,\; 1 \le r \Rightarrow \texttt{CoreCollision}\,X_A\,P_A\,r \Rightarrow \texttt{Engine}$.

The proof is strong induction (`Nat.strong_induction_on`): for $n < 2$ we have $n = 1$ and the
base `rank_one_coreCollision_engine` applies; for $n \ge 2$ we descend by `core_step` to $n-1$ and
apply the induction hypothesis. The off-by-one between collision-rank and state-rank, caught
during the formalisation of §31, is accounted for here: the induction runs on the collision rank,
and the descent strictly decreases it.

## The pigeonhole base: infinitude of starts $\Rightarrow$ collision

Now we exhibit the collision itself. Finiteness of the signature (`coreSig_fintype`) plus an
infinite injective family of starts yield two distinct starts with equal signature.

**Theorem 27.18** (`coreCollision_of_infinite`). Let $S \subseteq \iota$ be infinite,
$\mathrm{node} : \iota \to \texttt{RankNode}\,r$ injective on $S$ (distinct starts $\Rightarrow$
distinct cores), and let every $\mathrm{node}\,i$ ($i \in S$) be ambient-legal. Then
$\texttt{CoreCollision}\,X_A\,P_A\,r$.

The proof is pigeonhole by contradiction. If there is no collision, then
$\mathrm{coreSigOf} \circ \mathrm{node}$ is injective on $S$ (equal signatures of two distinct
cores would give a collision). But the image lies in the finite `CoreSig` (`Set.toFinite`), and an
injective map of an infinite $S$ into a finite type is impossible
(`Set.Finite.of_finite_image`) — contradicting $S.\texttt{Infinite}$. **This core is proved in
full**, with no inputs.

Hence the packaging of the carrier data:

**Theorem 27.19** (`freshStarts_to_coreCollision`). The carrier structure (infinitely many starts of
one sign and rank $1 \le r \le 4$, each an ambient-legal RankNode, distinct starts $\Rightarrow$
distinct cores) yields $\exists r',\; 1 \le r' \le 4 \wedge \texttt{CoreCollision}\,X_A\,P_A\,r'$.

## The whole machine: Engine from carrier data

**Theorem 27.20** (`product_core_engine_of_carrier`). Under the separating scale $6X_A+1 < P_A$,
$1 \le r \le 4$, and an infinite $S$ with starts $\mathrm{node}$ injective on $S$ and everywhere
ambient-legal — we obtain $\texttt{Engine}$.

The assembly: `product_core_pump_closed` (the finale *without* the hypothesis `core_step`, since
the step is proved as `core_step_proved` and the base is proved by arithmetic) is applied to
Theorem 27.19 (`freshStarts_to_coreCollision`). All the internal content — extensionality, the bound, finiteness,
the descent, the base, and the pigeonhole — is **proved in this file without `sorry`**.

What this *means* for the programme. We have travelled the path from "the trilemma resurrects one
rank higher" (§31) to a machine where the three defects are removed structurally by a single
choice of object.

**Conclusion.** Exactly **one** input remains open — `CarrierData`: the infinitude of nodeable
centres of a single layer, each yielding an ambient-legal RankNode of rank $1 \le r \le 4$ with
pairwise distinct cores.

> **Note (the honest boundary between the closed and the open).** We do not pass the reduction
> off as a proof. `product_core_engine_of_carrier` is a **conditional** theorem: it turns one
> explicit structural hypothesis (the carrier yields an infinite injective family of ambient-legal
> starts of fixed rank) into an Engine, and everything between the hypothesis and the Engine is
> machine-checked. The hole has not vanished — it has been compressed into `CarrierData` and
> precisely localised.

**Hypothesis (`CarrierData`) and the plan for closing it.** What is required: from the global
absorption at layer $A$, extract a type of centres $\iota$, an infinite subset $S$ of nodeable
centres, and a map $\mathrm{node} : \iota \to \texttt{RankNode}\,r$ such that (i) every centre
$m \in S$ yields a clean composite side $6m + \sigma = \prod_i a_i$ with factors $a_i > A$;
(ii) all the $a_i$ divide a common top legal side $N_0 \le 6X_A+1$ (ambient-legal); (iii) $r \le 4$;
(iv) distinct centres yield distinct cores.

The plan: points (i)–(iii) are the arithmetic of factoring the clean side and of the carrier
bound, worked out in the next chapter; point (iv) (injectivity) and, above all, the
**infinitude** of $S$ come from GlobalOldAbsorption and remain the last substantive input of the
entire programme.

It is exactly this factorisation of the clean composite side into a concrete `RankNode` — with the
arithmetic $a_i > A$, `AmbientLegal`, and $r \le 4$ proved — that we build in the next chapter
(§28, mkNode), reducing the open `CarrierData` to a single external fact: the infinitude of
nodeable centres.

<!--navbot-->

---

[← 26. Separating scale](26_SeparatingScale.md) · [Table of contents](00_Overview.md) · [28. MkNode →](28_MkNode.md)
<!--/navbot-->
