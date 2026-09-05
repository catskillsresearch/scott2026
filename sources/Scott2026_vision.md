---
source_pdf: Scott2026.pdf
ocr_method: cursor-vision-triple-merge
verification_status: draft
---

# Transcription (LLM vision OCR)


<!-- page 1 -->

# Interpreting Lambda Calculus in Domain-Valued Random Variables

**Robert Furber**  
Heriot-Watt University, Edinburgh, UK

**Radu Mardare**  
Heriot-Watt University, Edinburgh, UK

**Prakash Panangaden**  
McGill University, Montreal, Canada

**Dana Scott**  
Carnegie Mellon University, Pittsburgh, PA, USA

**Abstract**

We develop Boolean-valued domain theory and show how the lambda-calculus can be interpreted using domain-valued random variables. We focus on the reflexive domain construction rather than the language and its semantics. We develop the Boolean-valued set theory needed from scratch and then develop Boolean-valued domain theory on top of that. The notions of equality and partial order have to be given Boolean-valued interpretations; when we say that an equation is valid in the model we mean that its interpretation is the top element of the Boolean algebra.

**2012 ACM Subject Classification** Theory of computation; Theory of computation $\rightarrow$ Probabilistic computation; Theory of computation $\rightarrow$ Lambda calculus; Theory of computation $\rightarrow$ Denotational semantics

**Keywords and phrases** lambda calculus, domain theory, random variables

**Digital Object Identifier** 10.4230/LIPIcs.CSL.2026.48

**Related Version** *Full Version*: https://arxiv.org/abs/2112.06339

## 1 Introduction

There has been burgeoning interest in probabilistic programming languages in the last decade. The main motivation is building *compositional* models of probabilistic processes and performing inference on them [25, 16, 33]. For machine learning applications the notion of conditioning is fundamental and the striking results of [1, 2] show that this is a subtle issue.

The combination of probability and higher type programming has been both technically challenging and important for the development of semantics for such languages. There are a variety of approaches based on probabilistic coherence spaces [10] or cones [9], quasi-Borel spaces [31, 17, 32] and Boolean-valued models [3] which was based on Dana Scott’s vision [28]. Stochastic lambda-calculi have appeared [6, 7, 8] with important contributions to the understanding of probability theory at higher type. The work on quasi-Borel spaces gives a cartesian closed category that can serve as the foundation for a typed higher-order probabilistic programming language [17].

In [3] a Boolean-valued domain theory was developed. The idea is to use one of the standard set-theoretic models of the $\lambda$-calculus but interpreted in a suitable Boolean-valued universe of sets. However, the basic domain theoretic definitions of directed set, supremum, reflexive dcpo and continuity were interpreted as usual. The theory presented there is rather complicated and had artificial restrictions on the way randomness was handled. In the present paper a *completely* Boolean-valued point of view is adopted and even basic concepts, like equality and order, are all interpreted in a Boolean-valued logic. This leads to a much

© Robert Furber, Radu Mardare, Prakash Panangaden, and Dana Scott; licensed under Creative Commons License CC-BY 4.0

34th EACSL Annual Conference on Computer Science Logic (CSL 2026).

Editors: Stefano Guerrini and Barbara König; Article No. 48; pp. 48:1–48:20

Leibniz International Proceedings in Informatics

Schloss Dagstuhl – Leibniz-Zentrum für Informatik, Dagstuhl Publishing, Germany

<!-- page 2 -->

**48:2** · *Interpreting Lambda Calculus in Domain-Valued Random Variables*

simpler theory but still in line with the vision of [28]. The version of Boolean-valued domain theory used in the current paper supersedes [3] by working “internally”, by transferring theorems from ordinary logic to Boolean-valued logic as much as possible, rather than the “bare handed” approach of [3].

We show that untyped $\lambda$-calculus can be interpreted in domain-valued random variables. In order to employ the theory of Boolean-valued sets, for most of the article we actually use the Boolean-valued power set rather than random variables, and then show that there is an isomorphism between the two at the end. We focus on the reflexive domain construction rather than the language and its semantics.

The main contribution of this paper is the completely Boolean-valued reconstruction of domain theory. The notion of equality has to be interpreted in the Boolean algebra and when we say that an equation is valid in the model we mean that its interpretation is the top element of the domain.

What makes the theory of Boolean-valued sets necessary is that domain-valued random variables do not form a *continuous* dcpo. However, when “continuous dcpo” is given its interpretation in Boolean-valued sets, they are. The version of Boolean-valued sets we have used is the original version in terms of a cumulative hierarchy. If the reader prefers, they may rephrase the arguments results in terms of topos theory in a Boolean topos, and we outline the connection of the two in Section 3, though the only part of this theory that we use is the ability to define functions. As an example of how to apply Boolean-valued domain theory, we show that there exist two sets of integers, neither of which can be mapped to the other by a $\lambda$-definable function. The reason for choosing this example is that it shows that $\lambda$-calculus and its model based on domain-valued random variables are powerful enough to prove a fact that does not mention probability in its statement, and such that the proof is pure $\lambda$-calculus and probability and doesn’t need to pass via the equivalence between $\lambda$-definability and general recursion and applying the Kleene-Post theorem [20] that there are incomparable many-one degrees. The proof, however, is inspired by Spector’s probabilistic proof [30].

For reasons of space, the complete proofs of some results are omitted, even from the appendix. However, they can be found in the “related version” on the arxiv, linked above.

## 2 Background on Boolean-Valued Set Theory

In this section we describe how statements and proofs in ordinary set theory can be re-interpreted in a Boolean-valued sense. This interpretation is originally due to Scott and Solovay [26, 19, 5].

Throughout this section we let $A$ be an arbitrary complete Boolean algebra. It will play the role that the two-element Boolean algebra $2$ plays in ordinary logic. We can build up the class of $A$-valued sets, $V^A$, by considering an $A$-valued set $X$ to be a partial function that assigns to each element $x$ of its domain the amount, valued in $A$, that $x$ is an element of $X$. We build up $V^A$ by the following generalization of von Neumann’s construction:

$$
V^A_0 = \emptyset, \qquad V^A_{\alpha+1} = \{ f : V^A_\alpha \rightharpoonup A \}, \qquad V^A_\alpha = \bigcup_{\beta < \alpha} V^A_\beta \text{ for } \alpha \text{ a limit ordinal.}
$$

Then either informally, or using proper classes,

$$
V^A = \bigcup_{\alpha \in \mathbf{Ord}} V^A_\alpha.
$$

We use the term *$A$-valued set* for the elements of $V^A$, but we also will use the shorter term *$A$-set*, and this helps to avoid certain confusions arising from the term “valued”.

<!-- page 3 -->

We can then interpret $\in$, $\subseteq$ and $=$ by the following mutually recursive formulas:

$$
\|x \in X\| = \bigvee_{t \in \operatorname{dom} X} \|x = t\| \wedge X(t) \qquad \|X \subseteq Y\| = \bigwedge_{t \in \operatorname{dom} X} X(t) \Rightarrow \|t \in Y\|
$$

$$
\|x = y\| = \|x \subseteq y\| \wedge \|y \subseteq x\|.
$$

In the above, and all that follows, we use an operator precedence convention for $\bigvee$ and $\bigwedge$ that agrees with operator precedence for $\exists$ and $\forall$, so there is an implicit bracket around everything to the right of such a join or meet.

Recall that the first-order language of set theory, which we write as $\mathfrak{L}_{\mathrm{Set}}$, is the usual first-order language for a signature with equality and one two-place relation symbol, namely $\in$. We write $\mathfrak{L}_{\mathrm{Set}}(V^A)$ for this language extended with constants from $V^A$.

In any Boolean algebra, we can interpret the connectives of propositional logic. Using the completeness of $A$, we can interpret the universal quantifier as a meet and the existential quantifier as a join. All together, this gives us an interpretation of $\mathfrak{L}_{\mathrm{Set}}(V^A)$ in $V^A$.

**Theorem 1** ($V^A$ as a model).

(i) If $\phi \in \mathfrak{L}_{\mathrm{Set}}(V^A)$ is a theorem of ZFC set theory, then $\|\phi\| = 1$ in $V^A$.

(ii) The inference rules of first-order logic can be applied to theorems of ZFC set theory and statements about elements of $V^A$ in $\mathfrak{L}_{\mathrm{Set}}(V^A)$.

(iii) If $\|\exists x.\,\Phi(x, X_1, \dots, X_n)\| = a$, where $X_1, \dots, X_n \in V^A$ (and we allow $n = 0$), then there exists $X_0 \in V^A$ such that $\|\Phi(X_0, X_1, \dots, X_n)\| = a$.

The constructions of singletons $\{x\}^A$, unordered pairs $\{x,y\}^A$ and ordered pairs $(x,y)^A$ are done as usual in set theory, but interpreted in $V^A$. Details can be found in the arxiv version. For $X, Y \in V^A$ we define $X \times_A Y$ as follows.

$$
X \times_A Y : \{(x,y)^A \mid x \in \operatorname{dom}(X),\, y \in \operatorname{dom}(Y)\} \to A
$$

$$
(X \times_A Y)(x,y)^A = \|x \in X\| \wedge \|y \in Y\|.
$$

For each $A$-set $X$, the $A$-valued power set $\mathcal{P}^A(X)$ is defined by

$$
\operatorname{dom}(\mathcal{P}^A(X)) = \{u \in V^A \mid \operatorname{dom}(u) = \operatorname{dom}(X) \text{ and } \forall t \in \operatorname{dom}(u).\, u(t) \le X(t)\}
$$

$$
\mathcal{P}^A(X)(u) = 1
$$

For all $S, X \in V^A$ we have $\|S \in \mathcal{P}^A(X)\| = \|S \subseteq X\|$, which is how the power set axiom is proved for $V^A$. If $\Phi$ is a set-theoretic formula we can define the $A$-set

$$
\{x \in X \mid \Phi(x)\}^A : \operatorname{dom}(X) \to A \text{ by}
$$

$$
\{x \in X \mid \Phi(x)\}^A(t) = X(t) \wedge \|\Phi(t)\|,
$$

which proves the axiom of separation for $V^A$.

If we now consider von Neumann's universe $V$ of classic set theory constructed inductively on ordinals $\alpha \in \mathbf{Ord}$, then for each set $S \in V_\alpha$, there is a corresponding element $\check{S} \in V^A_\alpha$ defined recursively. The domain of $\check{S}$ is $\{\check{x} \mid x \in S\}$, and it is defined by:

$$
\check{\emptyset} = \emptyset, \quad \text{and } \check{S}(\check{x}) = 1 \text{ for all } x \in S.
$$

To describe how a statement in set theory about an ordinary set in $X \in V$ translates to a statement about $\check{X} \in V^A$, we need the notion of a $\Delta_0$ statement. Bounded quantifiers are those of the form $\forall x \in X.\,\Phi(x)$ and $\exists x \in X.\,\Psi(x)$, i.e. in the language of set theory $\forall x.\, x \in X \Rightarrow \Phi(x)$ and $\exists x.\, x \in X \wedge \Psi(x)$. A $\Delta_0$ formula $\Phi \in \mathfrak{L}_{\mathrm{Set}}(V^A)$ is one containing only bounded quantifiers. We have $\Delta_0$ invariance$^1$ [19, Lemma 14.21] or [5, Theorem 1.23 (v)].

$^1$ Note that Bell uses the alternative terminology “restricted” for $\Delta_0$.

<!-- page 4 -->

**48:4** · Interpreting Lambda Calculus in Domain-Valued Random Variables

▶ **Theorem 2** ($\Delta_0$ invariance). Let $\Phi(x_1, \ldots, x_n)$ be a $\Delta_0$-formula, whose free variables are $x_1, \ldots, x_n$. Let $X_1, \cdots, X_n \in V$. Then, $\Phi(X_1, \ldots, X_n) \Leftrightarrow \|\Phi(\check{X}_1, \ldots, \check{X}_n)\| = 1$.

We point out some useful consequences of Theorem 2. The statements “$S$ is a singleton whose only element is $x$”, “$S$ is an unordered pair of $x$ and $y$” and “$S$ is an ordered pair, first element $x$, second element $y$” are all $\Delta_0$ statements, and so the following all hold

$$
\widecheck{\{x\}} = \{\check{x}\}^A \qquad \widecheck{\{x, y\}} = \{\check{x}, \check{y}\}^A \qquad \widecheck{(x, y)} = (\check{x}, \check{y})^A.
$$

Another important consequence of Theorem 2 is that $\check{\omega}$ is the smallest inductive$^2$ $A$-set in $V^A$, so that $\check{\omega}$ is the $\omega$ of $V^A$. Given any set $X$, we say a subset $S \subseteq X$ is finite if there exists $n \in \omega$ and $f : n \to X$ such that $S = \operatorname{im}(f)$. We write $\mathcal{P}_{\mathrm{fin}}(X)$ for the set of all finite subsets of $X$. If we interpret this with $A$-sets, for each $X \in V^A$ we can define $\mathcal{P}_{\mathrm{fin}}^A(X)$ to be the set of finite $A$-subsets of $X$, using the axiom of separation. The following proposition is a consequence of the distributive law — see [21, 3.1.11].

▶ **Proposition 3.** For all sets $X$, $\|\mathcal{P}_{\mathrm{fin}}^A(\check{X}) = \widecheck{\mathcal{P}_{\mathrm{fin}}(X)}\| = 1$.

We can define the category $\mathbf{Set}_A$ from $V^A$ as follows. The class of objects is $V^A$, and for each $X, Y \in V^A$, the set of functions $\{X \xrightarrow{A} Y\} \in V^A$ can be defined using products, power set, and the axiom of separation. We define:

$$
\mathbf{Set}_A(X, Y) = \{f \in \operatorname{dom}(\{X \xrightarrow{A} Y\}) \mid \|f \in \{X \xrightarrow{A} Y\}\| = 1\}/{\sim},
$$

where $\sim$ is the equivalence relation defined by $f \sim g$ iff $\|f = g\| = 1$. Identity elements are defined as identity relations, and composition by composition of relations, which is well-defined with respect to $\sim$.

## 3 Boolean-Valued Setoids

We now discuss the kind of “Boolean-valued sets” that are essentially $A$-valued models of the theory of $=$. These can be considered an alternative description of either sheaves or separated presheaves on $A$, and are usually discussed in the more general case where $A$ is a Heyting algebra, such as in [12, 15, 24]. Although we will use only one definition of $A$-valued sets, the distinction between $A$-valued relations that satisfy the definition of a function *internally* and functions that do so gives us two distinct categories.

In order to distinguish the $A$-valued sets we will be discussing from elements of $V^A$, we call them $A$-valued setoids$^3$, or simply $A$-setoids. An $A$-setoid is a pair $(X, \|{=}\|_X)$ where $X$ is a set and $\|{=}\|_X : X \times X \to A$. The two axioms of $\|{=}\|_X$ are symmetry and transitivity, i.e.

$$
\forall x, y \in X.\,\|x = y\|_X = \|y = x\|_X
$$

$$
\forall x, y, z \in X.\,\|x = y\|_X \wedge \|y = z\|_X \leq \|x = z\|_X.
$$

So $A$-valued setoids are “$A$-valued partial equivalence relations”.

Since reflexivity is not assumed, the statement $\|x = x\|_X$ does not represent a tautology, but its intended interpretation is, in some sense, the degree to which $x \in X$, or the place where $x \in X$. So we define the notation $\varepsilon_X(x) = \|x = x\|_X$.

We say $(X, \|{=}\|_X)$ is total if $\|x = x\|_X = 1$ for all $x \in X$, i.e. if reflexivity holds; it is strict if $\|x = y\|_X = 1$ implies $x = y$.

---

$^2$ In the sense used to formulate the axiom of infinity in ZF.

$^3$ *Setoid* is a long-established term for a set equipped with an equivalence relation.

<!-- page 5 -->

**R. Furber, R. Mardare, P. Panangaden, and D. Scott** · **48:5**

▶ **Definition 4.** Let $(X, \|{=}\|_X)$ be an $A$-setoid. We say it is *complete*$^4$ if either, hence both, of the following equivalent properties holds:

(i) For any family of elements $(a_i)_{i \in I}$ in $A$ and corresponding family $(x_i)_{i \in I}$ in $X$ such that for all $i, j \in I$, $a_i \wedge a_j \le \|x_i = x_j\|_X$, there exists $x \in X$ such that for all $i \in I$, $a_i \le \|x_i = x\|_X$.

(ii) For any pairwise disjoint family of elements $(a_i)_{i \in I}$ in $A$ and corresponding family $(x_i)_{i \in I}$ in $X$ such that for all $i \in I$, $a_i \le \|x_i = x_i\|_X$, there exists $x \in X$ such that for all $i \in I$, $a_i \le \|x_i = x\|_X$.

▶ **Definition 5.** If $(X, \|{=}\|_X)$ is an $A$-setoid and $(Y, \|{=}\|_Y)$ is a set and a function $\|{=}\|_Y : Y \times Y \to A$, and $f : X \to Y$ is a bijection such that for all $x_1, x_2 \in X$:

$$
\|f(x_1) = f(x_2)\|_Y = \|x_1 = x_2\|_X,
$$

then we say $f$ is a *strict isomorphism*, and it follows that $(Y, \|{=}\|_Y)$ is an $A$-setoid, and is total, strict or complete iff $(X, \|{=}\|_X)$ is.

▶ **Definition 6.** The *product* $(X, \|{=}\|_X) \times (Y, \|{=}\|_Y)$ is defined to have

$$
\|(x, y) = (x', y')\|_{X \times Y} = \|x = x'\|_X \wedge \|y = y'\|_Y.
$$

▶ **Definition 7.** A predicate on $(X, \|{=}\|_X)$ is a function $S : X \to A$ such that:

(i) For all $x_1, x_2 \in X$, $\|x_1 = x_2\|_X \le S(x_1) \Leftrightarrow S(x_2)$.

(ii) For all $x \in X$, $S(x) \le \varepsilon_X(x)$.

A binary relation $X \to Y$ is simply a predicate on $X \times Y$.

This allows us to define a category of setoids with relations that satisfy the internal definition of a function (“relational functions”) as morphisms.

▶ **Definition 8.** The category $\mathbf{SetoidR}_A$ has $A$-setoids as objects and a morphism is a relation $f : X \to Y$ such that (additionally to (i) and (ii) from Definition 7):

(iii) For all $x \in X$, $y_1, y_2 \in Y$, $f(x, y_1) \wedge f(x, y_2) \le \|y_1 = y_2\|_Y$.

(iv) For all $x \in X$, $\varepsilon_X(x) \le \bigvee_{y \in Y} f(x, y)$.

The identity function $\mathrm{id}_X : X \to X$ is defined by: $\mathrm{id}_X(x_1, x_2) = \|x_1 = x_2\|_X$.

Composition of functions $f : X \to Y$ and $g : Y \to Z$ is defined by

$$
(g \circ f)(x, z) = \bigvee_{y \in Y} f(x, y) \wedge g(y, z).
$$

We define the category of $A$-setoids and “functional functions”, $\mathbf{SetoidF}_A$, as follows.

▶ **Definition 9.** The category $\mathbf{SetoidF}_A$ has $A$-setoids as objects. The morphisms are defined starting with an $A$-setoid:

$$
X \multimap Y = \{f : X \to Y \mid \forall x_1, x_2 \in X.\, \|x_1 = x_2\|_X \le \|f(x_1) = f(x_2)\|_Y\}
$$

$$
\|f_1 = f_2\|_{X \multimap Y} = \bigwedge_{x \in X} \varepsilon_X(x) \Rightarrow \|f_1(x) = f_2(x)\|_Y.
$$

---

$^4$ This definition is slightly different from that used in [12, 4.10, 4.11] and elsewhere, which would not suit us because under that definition $\mathcal{P}^A(X)$ is not complete, when considered as an $A$-setoid in the sense we will define in Definition 14.

<!-- page 6 -->

**48:6** · Interpreting Lambda Calculus in Domain-Valued Random Variables

Then the hom set $\mathbf{SetoidF}_A(X, Y)$ is the quotient set of *this*,$^5$ i.e. $X \multimap Y$ modulo the equivalence relation:

$$f_1 \sim f_2 \text{ iff } \forall x \in X.\, \varepsilon_X(x) \le \|f_1(x) = f_2(x)\|_Y.$$

Identity maps and composition are defined as for functions.

The category $\mathbf{SetoidF}_A$ is called $\mathbf{Mod}_0(A)$ in [24, Definition 5.2], where it is proved to be a quasi-topos. The full subcategory on non-empty$^6$ complete $A$-setoids is a topos [24, Proposition 5.6 (ii)] equivalent to the category of sheaves on the canonical topology on $A$.

Mapping a functional function to its graph defines a faithful functor from $\mathbf{SetoidF}_A \to \mathbf{SetoidR}_A$.

▶ **Definition 10.** *The following defines a faithful functor $\gamma : \mathbf{SetoidF}_A \to \mathbf{SetoidR}_A$. On objects, $\gamma(X, \|{=}\|_X) = (X, \|{=}\|_X)$. For $f \in \mathbf{SetoidF}_A(X, Y)$, we define*

$$\gamma(f)(x, y) = \varepsilon_X(x) \wedge \|f(x) = y\|_Y.$$

We can formulate a notion of poset that does not require us to define $\|{=}\|_X$ but can instead be defined in terms of it. It turns out to be useful in the general theory, as well as for dealing with posets that are $A$-setoids or $A$-sets.

▶ **Definition 11.** *An $A$-poset is a pair $(X, \|{\le}\|_X)$, where $X$ is a set and $\|{\le}\|_X : X \times X \to A$ is such that for all $x_1, x_2, x_3 \in X$:*

(i) $\|x_1 \le x_2\|_X \wedge \|x_2 \le x_3\|_X \le \|x_1 \le x_3\|_X$.

(ii) $\|x_1 \le x_2\|_X \le \|x_1 \le x_1\|_X \wedge \|x_2 \le x_2\|_X$.

*We then define $\|{=}\|_X$ by*

$$\|x_1 = x_2\|_X = \|x_1 \le x_2\|_X \wedge \|x_2 \le x_1\|_X. \qquad (1)$$

*Then $(X, \|{=}\|_X)$ is an $A$-setoid, and $\|{\le}\|_X$ is a reflexive, antisymmetric, transitive relation when these statements are interpreted in the $A$-valued sense. If $(X, \|{=}\|_X)$ is an $A$-setoid and $\|{\le}\|_X$ is a relation that is reflexive, antisymmetric and transitive, in the $A$-valued sense, then $(X, \|{\le}\|_X)$ is an $A$-poset in the above sense, and $\|{=}\|_X$ satisfies (1).*

Since $\|{=}\|_X$ is defined in terms of $\|{\le}\|_X$, the following fact is convenient for proving that a function on underlying sets $f : X \to Y$ not only defines an element of $\mathbf{SetoidF}_A(X, Y)$ but also a monotone function in the $A$-valued sense.

▶ **Lemma 12.** *Let $(X, \|{\le}\|_X), (Y, \|{\le}\|_Y)$ be $A$-posets, and suppose that $f : X \to Y$ is $A$-monotone in the sense$^7$ that for all $x_1, x_2 \in X$, $\|x_1 \le x_2\|_X \le \|f(x_1) \le f(x_2)\|_Y$. Then $f \in X \multimap Y$. Every $f \in \mathbf{SetoidF}_A(X, Y)$ that is monotone in the $A$-valued interpretation of the term is of this form.*

The following definition and theorem are based on [23, Proposition 3.3].

---

$^5$ Monro calls these *admissible functions* in [24, Definition 5.2].

$^6$ We mean not having $\emptyset$ as an underlying set. It is still allowed, and necessary, to have sets that do not assign any value other than 0 to any element, which are “empty” in terms of Boolean-valued logic.

$^7$ This is monotonicity using the interpretation of logic in Section 2.

<!-- page 7 -->

**R. Furber, R. Mardare, P. Panangaden, and D. Scott** · **48:7**

▶ **Definition 13.** Let $(X, \|{=}\|_X), (Y, \|{=}\|_Y)$ be $A$-setoids such that $Y$ is complete, and let $f \in \mathbf{SetoidR}_A(X, Y)$. For each $x \in X$, there exists $\mathcal{F}(f)(x) \in Y$ such that

$$f(x, y) \le \|\mathcal{F}(f)(x) = y\|_Y. \qquad (2)$$

Any choice of $\mathcal{F}(f)(x)$ for all $x \in X$ defines an element $\mathcal{F}(f) \in \mathbf{SetoidF}_A(X, Y)$ such that $\gamma(\mathcal{F}(f)) = f$, and in fact this establishes a $\mathbf{SetoidF}_A$ isomorphism $\mathbf{SetoidR}_A(X, Y) \cong \mathbf{SetoidF}_A(X, Y)$.

Every $A$-set defines an $A$-setoid as follows.

▶ **Definition 14.** Let $X \in V^A$. Define $\|{=}\|_X : \mathrm{dom}(X) \times \mathrm{dom}(X) \to A$ by

$$\|x = y\|_X = \|x \in X\| \wedge \|y \in X\| \wedge \|x = y\|. \qquad (3)$$

Then $(\mathrm{dom}(X), \|{=}\|_X)$ is an $A$-setoid, which we write $\mathrm{Oid}(X)$ when we need to be unambiguous. When we speak of elements of $\mathrm{Oid}(X)$, we mean elements of the underlying set of $\mathrm{Oid}(X)$, i.e. elements of $\mathrm{dom}(X)$, following the usual convention for sets with structure.

▶ **Definition 15.** Let $X \in V^A$. For each $S \in V^A$ such that $\|S \subseteq X\| = 1$, then $e(S)$, defined as follows, is a predicate on $\mathrm{Oid}(X)$:

$$e(S)(x) = \|x \in S\|,$$

where $x \in \mathrm{Oid}(X)$. In particular, this holds if $S \in \mathrm{dom}(\mathcal{P}^A(X))$.

▶ **Definition 16.** The following defines $\mathrm{Oid} : \mathbf{Set}_A \to \mathbf{SetoidR}_A$ as a functor, where $f : X \to Y$ is in $\mathbf{Set}_A$:

$$\mathrm{Oid}(f)(x, y) = \|(x, y)^A \in f\|.$$

This functor is full, faithful and essentially surjective, so $\mathbf{Set}_A \simeq \mathbf{SetoidR}_A$.

▶ **Theorem 17.** For each $X \in V^A$, $\mathrm{Oid}(\mathcal{P}^A(X))$ is complete. Moreover, if $\Phi$ is a formula of $\mathcal{L}_{\mathrm{Set}}(V^A)$ and $\|\exists S \in \mathcal{P}^A(X).\ \Phi(S, \dots)\| = a \in A$, then there exists $S \in \mathrm{Oid}(\mathcal{P}^A(X))$ such that $\|\Phi(S, \dots)\| = a$.

▶ **Corollary 18.** For each $X, Y \in V^A$, $\mathrm{Oid}(\mathcal{P}^A(X \times_A Y))$ and $\mathrm{Oid}(\{X \xrightarrow{A} Y\})$ are complete, and if we prove a relation or a function exists in the Boolean-valued sense, satisfying some formula $\Phi \in \mathcal{L}_{\mathrm{Set}}(V^A)$, then there exists a corresponding element of $\mathrm{Oid}(\mathcal{P}^A(X \times_A Y))$ or $\mathrm{Oid}(\{X \xrightarrow{A} Y\})$ satisfying $\Phi$.

## 4 Models of Untyped Lambda-calculus in Boolean-valued sets

In this section we show how to model untyped $\lambda$-calculus in $A$-valued sets. We use the Engeler model [11] as the main example. We will repeatedly use Theorem 1 to prove statements in $V^A$ by proving them in set theory first. The reader who would prefer to use a topos formulation might prefer to use the categorical formulation of the Engeler model from [18].

### 4.1 Background on Domain Theory

A *dcpo* $(D, \le)$ is a poset that is directed complete, i.e. such that every directed set has a supremum. Every complete lattice is a dcpo. The least element of a dcpo $(D, \le)$, if it exists, is called the *bottom element* and is written $\bot$. In a dcpo $D$, where $d, e \in D$, we say that $d$

<!-- page 8 -->

**48:8** · Interpreting Lambda Calculus in Domain-Valued Random Variables

is way below $e$, written $d \ll e$, if for each directed set $(e_i)_{i \in I}$ such that $e \le \bigvee_{i \in I} e_i$, there exists some $j \in I$ such that $d \le e_j$. The relation $\ll$ is transitive and antisymmetric, but in general is neither reflexive nor irreflexive. We write $\Downarrow d = \{e \in D \mid e \ll d\}$. A dcpo $D$ is called *continuous* if for all $d \in D$, the set $\Downarrow d$ is directed and $d = \bigvee \Downarrow d$. A continuous dcpo is called a *domain*. A complete lattice that is continuous as a dcpo is called a *continuous lattice*. A *basis* or *base* for a domain $D$ is a subset $B \subseteq D$ such that for all $d \in D$, $\Downarrow d \cap B$ is directed, and $d = \bigvee (\Downarrow d \cap B)$. It follows that if $D$ is continuous, then $D$ is a base for $D$. If $D$ has a countable base, we say it is a *countably-based domain*. See [14] for more related concepts.

If $D$ and $E$ are dcpos, a function $f : D \to E$ is said to be *Scott continuous* if it is monotone and preserves directed suprema. We write $[D \to E]$ for the set of Scott-continuous maps $D \to E$. This is a dcpo when given the pointwise ordering, and directed suprema are calculated pointwise. When we refer to this as a dcpo, we always use this structure. The Scott topology on a dcpo $D$ is the topology whose open sets are the sets $U \subseteq D$ such that $U$ is an up set and for all directed sets $(d_i)_{i \in I}$ such that $\bigvee_{i \in I} d_i \in U$ there exists $i \in I$ such that $d_i \in U$. If $D$ and $E$ are dcpos, a function $f : D \to E$ is Scott continuous iff it is a continuous map from $D$ to $E$ equipped with their respective Scott topologies.

▶ **Definition 19.** A reflexive dcpo is a triple $(D, \mathbf{fun}, \mathbf{lam})$, where $D$ is a dcpo with bottom$^8$, and $\mathbf{fun} : D \to [D \to D]$ and $\mathbf{lam} : [D \to D] \to D$ are Scott-continuous maps making $[D \to D]$ a retract of $D$, i.e. $\mathbf{fun} \circ \mathbf{lam} = \mathrm{id}_{[D \to D]}$. A reflexive dcpo is *extensional* iff $\mathbf{fun}$, or equivalently $\mathbf{lam}$, is an isomorphism, i.e. iff additionally $\mathbf{lam} \circ \mathbf{fun} = \mathrm{id}_D$.

It is often convenient to formulate this notion using the uncurried form of $\mathbf{fun}$, which is to say, we can equivalently define a reflexive dcpo to be a triple $(D, \cdot, \mathbf{lam})$ where $D$ is a dcpo with bottom, and $\cdot : D \times D \to D$ and $\mathbf{lam} : [D \to D] \to D$ are Scott-continuous maps such that for each $f \in [D \to D]$ and $d \in D$ we have $\mathbf{lam}(f) \cdot d = f(d)$.

The language of untyped $\lambda$-calculus can be interpreted in a reflexive dcpo as follows. Given a reflexive dcpo $(D, \cdot, \mathbf{lam})$, and a set of variables $\mathrm{Var}$, a valuation is a partial function $\rho : \mathrm{Var} \to D$. We also choose a set of constants $\mathfrak{K} \subseteq D$, which is allowed to be any subset, including $\emptyset$ and $D$ itself. We then define the language of $\lambda$-calculus $\Lambda(D, \mathrm{Var}, \mathfrak{K})$ as follows.

▶ **Definition 20.** The language $\Lambda(D, \mathrm{Var}, \mathfrak{K})$ is defined inductively by the rules

$$
\frac{x \in \mathrm{Var}}{x \in \Lambda(D, \mathrm{Var}, \mathfrak{K})}
\qquad
\frac{d \in \mathfrak{K}}{d \in \Lambda(D, \mathrm{Var}, \mathfrak{K})}
$$

$$
\frac{x \in \mathrm{Var} \quad M \in \Lambda(D, \mathrm{Var}, \mathfrak{K})}{\lambda x.\, M \in \Lambda(D, \mathrm{Var}, \mathfrak{K})}
\qquad
\frac{M \in \Lambda(D, \mathrm{Var}, \mathfrak{K}) \quad N \in \Lambda(D, \mathrm{Var}, \mathfrak{K})}{MN \in \Lambda(D, \mathrm{Var}, \mathfrak{K})}
$$

We write $\Lambda(\mathrm{Var})$ for $\Lambda(D, \mathrm{Var}, \emptyset)$, since this does not depend on $D$. The elements of $\Lambda(\mathrm{Var})$ are called *pure $\lambda$-terms*. We write $\mathrm{fv}(M)$ for the set of free variables of $M$, defined as usual.

We make the following observation about how the above definition is formulated in set theory.$^9$

▶ **Example 21.** There exist $\Delta_0$ formulas $\Lambda(D, \mathrm{Var}, \mathfrak{K})$-inductive and $\Lambda(\mathrm{Var})$-inductive, such that the sets $\Lambda(D, \mathrm{Var}, \mathfrak{K})$ and $\Lambda(\mathrm{Var})$ are respectively definable as the smallest sets satisfying their corresponding formula.

---

$^8$ This is what is meant by a cpo in [4, Definition 1.2.1 (ii)].

$^9$ This is needed to make the proof of Proposition 22 and later results that deal with viewing the syntax of $\lambda$-calculus from inside $V^A$ more comprehensible.

<!-- page 9 -->

Indeed, to define $\Lambda(\mathrm{Var})\text{-inductive}$ and $\Lambda(D, \mathrm{Var}, \mathfrak{K})\text{-inductive}$, we need a way to represent the syntax of $\lambda$-calculus. For example, we could take the ordinals $0$ to mean a variable, $1$ a $\lambda$-abstraction, $2$ an application and $3$ a constant, so that a variable appears as $(0, x)$ for $x \in \mathrm{Var}$, a $\lambda$-abstraction as $(1, (x, M))$ where $x \in \mathrm{Var}$ and $M$ is a $\lambda$-term, an application as $(2, (M, N))$ where $M, N$ are $\lambda$-terms, and a constant as $(3, d)$ where $d \in \mathfrak{K}$.

Then we can define:

$$
\begin{aligned}
\Lambda(\mathrm{Var})\text{-inductive}(X) &= (\forall x \in \mathrm{Var}.\, \exists p \in X.\, p = (0, x)) \\
&\wedge (\forall x \in \mathrm{Var}.\, \forall M \in X.\, \exists p \in X.\, p = (1, (x, M))) \\
&\wedge (\forall M \in X.\, \forall N \in X.\, \exists p \in X.\, p = (2, (M, N))).
\end{aligned}
$$

Strictly speaking this is not quite a $\Delta_0$ formula, but it is not difficult to see that the statements $p = (0, x)$, $p = (1, (x, M))$ and $p = (2, (M, N))$ are expressible as $\Delta_0$ formulas (with the usual set-theoretic representations of ordered pairs). Then, we define:

$$
\Lambda(D, \mathrm{Var}, \mathfrak{K})\text{-inductive}(X) = \Lambda(\mathrm{Var})\text{-inductive}(X) \wedge (\forall d \in \mathfrak{K}.\, \exists p \in X.\, p = (3, d)).
$$

Then, $\Lambda(\mathrm{Var})$ and $\Lambda(D, \mathrm{Var}, \mathfrak{K})$ are the least sets satisfying their respective formulas.

▶ **Proposition 22.** Let $\mathrm{Var}$ be a set$^{10}$. For any complete Boolean algebra $A$, there exists$^{11}$ $\Lambda(\widecheck{\mathrm{Var}})^A$ that satisfies the definition of $\Lambda(\widecheck{\mathrm{Var}})$ in the Boolean-valued sense, i.e.

$$
\|\Lambda(\widecheck{\mathrm{Var}})\text{-inductive}(\Lambda(\widecheck{\mathrm{Var}})^A)\| = 1
$$

and for all $X \in V^A$ such that $\|\Lambda(\widecheck{\mathrm{Var}})\text{-inductive}(X)\| = 1$, we have $\|\Lambda(\widecheck{\mathrm{Var}})^A \subseteq X\| = 1$. Then $\|\widecheck{\Lambda(\mathrm{Var})} = \Lambda(\widecheck{\mathrm{Var}})^A\| = 1$.

The equational theory of $\lambda$-calculus, called $\boldsymbol{\lambda}$, is described following [4]:

▶ **Definition 23.** Sentences of $\boldsymbol{\lambda}$ are of the form $M = N$, where $M, N \in \Lambda(\mathrm{Var})$. The theory $\boldsymbol{\lambda}$ is generated by the following rules, under modus ponens and $\alpha$-conversion.

(i) $(\lambda x.M)N = M[x := N]$, where $M[x := N]$ is capture-avoiding substitution of $N$ for $x$.

(ii) $M = M$.

(iii) $M = N \Rightarrow N = M$.

(iv) $M = N,\, N = L \Rightarrow M = L$.

(v) $M = N \Rightarrow MZ = NZ$.

(vi) $M = N \Rightarrow ZM = ZN$.

(vii) $M = N \Rightarrow \lambda x.M = \lambda x.N$.

We write $\boldsymbol{\lambda} \vdash M = N$ to say that the equation $M = N$ is derivable in the theory $\boldsymbol{\lambda}$.

▶ **Example 24.** Here is a brief description of the set-theoretic formulation of $\boldsymbol{\lambda}$. We can simply consider it to be a subset of $\Lambda(\mathrm{Var}) \times \Lambda(\mathrm{Var})$, and interpret $\boldsymbol{\lambda} \vdash M = N$ as $(M, N) \in \boldsymbol{\lambda}$. We can define a formula $\boldsymbol{\lambda}\text{-inductive}(S)$, which we no longer require to be $\Delta_0$, that encodes the rules of forming $\boldsymbol{\lambda}$ from Definition 23, and then $\boldsymbol{\lambda}$ can be characterized as the least set (with respect to $\subseteq$) such that $\boldsymbol{\lambda}\text{-inductive}(\boldsymbol{\lambda})$. This allows us to define $\boldsymbol{\lambda}^A$ in $V^A$. We can then prove that $\|\check{\boldsymbol{\lambda}} \subseteq \boldsymbol{\lambda}^A\| = 1$ by induction on the structure of an element of $\boldsymbol{\lambda}$.

---

$^{10}$ Not Boolean-valued, just the usual kind of set.

$^{11}$ By Theorem 1 (i) and (iii).

<!-- page 10 -->

**48:10 · Interpreting Lambda Calculus in Domain-Valued Random Variables**

▶ **Definition 25.** Following [4, Definition 5.4.2], we define the interpretation of $\lambda$-terms from $M \in \Lambda(D, \mathrm{Var}, \mathfrak{K})$ in $D$, using a valuation $\rho$ such that $\mathrm{fv}(M) \subseteq \mathrm{dom}(\rho)$, by

$$
\begin{aligned}
\llbracket x \rrbracket_\rho &= \rho(x) & x \in \mathrm{Var} \\
\llbracket k \rrbracket_\rho &= k & k \in \mathfrak{K} \\
\llbracket MN \rrbracket_\rho &= \llbracket M \rrbracket_\rho \cdot \llbracket N \rrbracket_\rho \\
\llbracket \lambda x.\, M \rrbracket_\rho &= \mathbf{lam}(\mathbb{\lambda} d.\, \llbracket M \rrbracket_{\rho(x := d)}),
\end{aligned}
$$

where $\mathbb{\lambda}$ is the “meta-lambda”, and $\rho(x := d)$ is the partial function where $\mathrm{dom}(\rho(x := d)) = \mathrm{dom}(\rho) \cup \{x\}$ and

$$
\rho(x := d)(y) = \begin{cases} \rho(y) & \text{if } y \in \mathrm{dom}(\rho) \setminus \{x\} \\ d & \text{if } y = x \end{cases}
$$

This is proved to define a model of $\lambda$-calculus in [4, Theorem 5.4.4], which is to say, that for all $M, N \in \Lambda(D, \mathrm{Var})$, if $\boldsymbol{\lambda} \vdash M = N$, then for all valuations $\rho$, $\llbracket M \rrbracket_\rho = \llbracket N \rrbracket_\rho$. For closed terms $M \in \Lambda(D, \mathrm{Var}, \mathfrak{K})$, we write $\llbracket M \rrbracket$ for $\llbracket M \rrbracket_\emptyset$.

We now give the Boolean-valued version.

▶ **Theorem 26.** Let $D \in V^A$ such that the $A$-setoid of $D$ is strict, total and complete, and let there be $\mathbf{lam}$ and $\cdot$ in $V^A$ such that $\|(D, \mathbf{lam}, \cdot)\ \text{is a reflexive dcpo}\| = 1$. And take $\mathrm{Var}$ to be a set of variables and $\mathfrak{K} \in V^A$ such that $\|\mathfrak{K} \subseteq D\| = 1$ an $A$-set of constants. Then for each $\rho$ that defines a partial function from $\mathrm{Var}$ to $D$, there are functions $\llbracket \cdot \rrbracket^A_\rho \in \mathbf{SetoidF}_A(\Lambda(D, \check{\mathrm{Var}}, \mathfrak{K})^A, D)$ and $\llbracket \cdot \rrbracket^A_\rho \in \mathbf{SetoidF}_A(\widecheck{\Lambda(\mathrm{Var})}, D)$ satisfying Definition 25 in the $A$-valued sense. Furthermore, for all $M, N \in \Lambda(\mathrm{Var})$, if $\boldsymbol{\lambda} \vdash M = N$, then for all $\rho$ we have $\llbracket \check{M} \rrbracket_\rho = \llbracket \check{N} \rrbracket_\rho$.

### 4.2 The Engeler Model

We start with a basic result about the power set.

▶ **Proposition 27.** For any set $X$, the power set $\mathcal{P}(X)$, when ordered using the subset relation $\subseteq$, is a dcpo (in fact, a complete lattice). If $S, T \in \mathcal{P}(X)$, $S \ll T$ iff $S$ is finite and $S \subseteq T$. The set of finite sets $\mathcal{P}_{\mathrm{fin}}(X)$ is a base, and if $X$ is countable, it is a countable base.

We can then apply this in $V^A$ as follows.

▶ **Proposition 28.** For any $X \in V^A$, the $A$-set $\mathcal{P}^A(X)$, ordered with the subset relation, is a continuous lattice with base $\mathcal{P}^A_{\mathrm{fin}}(X)$, interpreted in the $A$-valued sense. As an $A$-setoid, $\mathcal{P}^A(X)$ is complete and total. If $X = \check{Y}$, then $\widecheck{\mathcal{P}_{\mathrm{fin}}(Y)}$ is a base, and $\mathcal{P}^A(\check{Y})$ is strict.

We define the Engeler model [11, 4], an adaptation of the Scott-Plotkin graph model that uses set-theoretic operations instead of Gödel numbering, as follows.$^{12}$ Let $E_0 = \{\emptyset\}$. We define $E_{n+1} = (\mathcal{P}_{\mathrm{fin}}(E_n) \times E_n) \uplus E_n$ and $E = \bigcup_{n=0}^{\infty} E_n$. Then we have a map $(\cdot, \cdot) : \mathcal{P}_{\mathrm{fin}}(E) \times E \to E$ defined by pairing, since for each $S \in \mathcal{P}_{\mathrm{fin}}(E)$ we have $S \subseteq E_n$ for some $n \in \mathbb{N}$. For reasons that will become clear later, we express the existence of the Engeler model in the following manner.

---

$^{12}$ What we really need of $E$ is for it to be countable, non-empty, and an algebra of the functor $\mathcal{P}_{\mathrm{fin}} \times \mathrm{Id}$, such that the structure map $\mathcal{P}_{\mathrm{fin}}(E) \times E \to E$ is injective, which implies $E$ must be infinite. We cannot use the initial algebra of $\mathcal{P}_{\mathrm{fin}} \times \mathrm{Id}$, because it is $\emptyset$.

<!-- page 11 -->

**48:11 · Interpreting Lambda Calculus in Domain-Valued Random Variables**

▶ **Proposition 29.** Let $E$ be a set equipped with an injective mapping $(-, -) : \mathcal{P}_{\mathrm{fin}}(E) \times E \to E$. Define $\mathbf{lam} : [\mathcal{P}(E) \to \mathcal{P}(E)] \to \mathcal{P}(E)$ and $\cdot : \mathcal{P}(E) \times \mathcal{P}(E) \to \mathcal{P}(E)$ by

$$
\mathbf{lam}(f) = \{(K, q) \mid q \in f(K)\} = \{x \in E \mid \exists K \in \mathcal{P}_{\mathrm{fin}}(E), q \in f(K).\, x = (K, q)\}
$$

$$
F \cdot X = \{q \in E \mid \exists K \in \mathcal{P}_{\mathrm{fin}}(E).\, K \subseteq X \text{ and } (K, q) \in F\},
$$

where $f \in [\mathcal{P}(E) \to \mathcal{P}(E)]$, and $F, X \in \mathcal{P}(E)$. Then $(\mathcal{P}(E), \cdot, \mathbf{lam})$ is a reflexive dcpo.

We can now build the Engeler model in $V^A$, as follows.

▶ **Theorem 30.** Let $E$ be the set defined before Proposition 29. $(\mathcal{P}^A(\check{E}), \|\subseteq\|, \cdot, \mathbf{lam})$ is an $A$-valued reflexive dcpo, where $\cdot$ and $\mathbf{lam}$ are defined by the $A$-valued interpretation of the definitions given in Proposition 29.

By combining Theorem 30 with Proposition 28 and Theorem 26, we obtain a function $\llbracket \cdot \rrbracket^A$ that interprets $\lambda$-terms in a manner that respects provable equations between them. The following lemma shows that if we only use pure $\lambda$-terms we do not get anything new by using $\mathcal{P}^A(\check{E})$ instead of $\mathcal{P}(E)$ as a model of $\lambda$-calculus.

▶ **Lemma 31.** Let $M \in \Lambda(\mathrm{Var})$ and $\rho$ a valuation such that $\mathrm{fv}(M) \subseteq \mathrm{dom}(\rho)$, and consider $\llbracket \cdot \rrbracket^A$ and $\llbracket \cdot \rrbracket$ as defined for $\mathcal{P}^A(\check{E})$ and $\mathcal{P}(E)$ respectively. Then $\|\llbracket \check{M} \rrbracket^A_{\check{\rho}} = \llbracket M \rrbracket_\rho\| = 1$. In particular, since $\emptyset = \check{\emptyset}$, if $M$ is closed we have $\|\llbracket \check{M} \rrbracket^A = \llbracket M \rrbracket\| = 1$.

### 4.3 Injective Spaces and Oracles

We can encode the Booleans $\{\bot, \top\}$, and natural numbers $\mathbb{N}$ in $\lambda$-calculus in several ways, e.g. with the Church numerals. The details of the encoding do not matter, only the following.

▶ **Definition 32.** Let $(D, \mathbf{fun}, \mathbf{lam})$ be a reflexive dcpo, and let $\bot, \top$ be closed $\lambda$-terms and $(c_n)_{n \in \mathbb{N}}$ a family of closed $\lambda$-terms. We say $(D, \mathbf{fun}, \mathbf{lam}, \bot, \top, (c_n)_{n \in \mathbb{N}})$ is a reflexive dcpo with numerals if

(i) $\llbracket \bot \rrbracket$ and $\llbracket \top \rrbracket$ are distinct elements of $D$.

(ii) There exists a closed $\lambda$-term $\mathbf{if}$ such that for all $\lambda$-terms $M, N$, $\boldsymbol{\lambda} \vdash \mathbf{if}\,\top\, M N = M$ and $\boldsymbol{\lambda} \vdash \mathbf{if}\,\bot\, M N = N$.

(iii) There exist closed $\lambda$-terms $\mathbf{succ}$ and $\mathbf{pred}$ representing the successor and predecessor operations on $(c_n)_{n \in \mathbb{N}}$, i.e. for all $n \in \mathbb{N}$, $\boldsymbol{\lambda} \vdash \mathbf{succ}\, c_n = c_{n+1}$ and $\boldsymbol{\lambda} \vdash \mathbf{pred}\, c_{n+1} = c_n$ and $\boldsymbol{\lambda} \vdash \mathbf{pred}\, c_0 = c_0$.

(iv) There exists a closed $\lambda$-term $\mathbf{0}^?$ such that $\boldsymbol{\lambda} \vdash \mathbf{0}^?\, c_0 = \top$ and for all $n > 0$, $\boldsymbol{\lambda} \vdash \mathbf{0}^?\, c_n = \bot$.

▶ **Proposition 33.** The Church Booleans and Church numerals make the Engeler model into a reflexive continuous lattice with numerals.

▶ **Corollary 34.** The Engeler model in $V^A$, as described in Theorem 30, is a reflexive continuous lattice with numerals, when given ($\check{-}$ of) the Church Booleans and Church numerals, with this whole statement being interpreted in $V^A$.

In the following, for a set $A \subseteq \mathbb{N}$, we write $\chi_A$ for the function $A \to 2$ such that

$$
\chi_A(x) = \begin{cases} 1 & \text{if } x \in A \\ 0 & \text{if } x \notin A \end{cases},
$$

while if $\{\bot, \top\}$ are part of the structure of a reflexive dcpo with numerals $D$, we write $\chi_A^D$ for the function $\mathbb{N} \to \{\llbracket \bot \rrbracket, \llbracket \top \rrbracket\}$ such that:

$$
\chi_A^D(x) = \begin{cases} \llbracket \top \rrbracket & \text{if } x \in A \\ \llbracket \bot \rrbracket & \text{if } x \notin A \end{cases}.
$$

<!-- page 12 -->

**48:12 · Interpreting Lambda Calculus in Domain-Valued Random Variables**

Every dcpo is a $T_0$ topological space when equipped with its Scott topology [14]. And a $T_0$ topological space $X$ is injective for subspace embeddings in the category of $T_0$-spaces iff $X$ is a continuous lattice equipped with the Scott topology [27]. This has useful consequences for representations of the natural numbers in reflexive dcpos that are continuous lattices.

▶ **Lemma 35.** Let $(D, \mathbf{fun}, \mathbf{lam}, \perp, \top, (c_n)_{n \in \mathbb{N}})$ be a reflexive dcpo with numerals. Then:

(i) $\{\llbracket \perp \rrbracket, \llbracket \top \rrbracket\}$ and $\{\llbracket c_n \rrbracket\}_{n \in \mathbb{N}}$ are discrete in the Scott topology of $D$, and also are distinct elements, i.e. $\llbracket c_m \rrbracket = \llbracket c_n \rrbracket$ implies $m = n$.

If $D$ is additionally a continuous lattice, then:

(ii) For every set $A \subseteq \mathbb{N}$, there is a $d_g \in D$ such that for all $n \in \mathbb{N}$, $d_g \cdot \llbracket c_n \rrbracket = \chi_A^D(n)$.

We can now define a pre-order on sets of integers to be used in the example (Theorem 43). Readers familiar with recursion theory will see that it is the $\lambda$-calculus version of comparability of many-one degrees [29, Definition 4.8 (i), (iii)].

▶ **Proposition 36.** Let $D$ be a reflexive continuous lattice with numerals. The following are equivalent for $S_1, S_2 \subseteq \mathbb{N}$, in which case we write $S_1 \leq_m S_2$:

(i) There exists a closed $\lambda$-term $M \in \Lambda(D, \mathrm{Var})$ such that for all $n \in \mathbb{N}$, there exists $m \in \mathbb{N}$ such that $\boldsymbol{\lambda} \vdash M c_n = c_m$, and there exist $d_{S_1}, d_{S_2} \in D$ such that for all $n \in \mathbb{N}$, $\llbracket d_{S_1} c_n \rrbracket = \chi_{S_1}^D(n)$, $\llbracket d_{S_2} c_n \rrbracket = \chi_{S_2}^D(n)$ and $\llbracket d_{S_2} (M c_n) \rrbracket = \llbracket d_{S_1} c_n \rrbracket$.

(ii) There exists a closed $\lambda$-term $M \in \Lambda(D, \mathrm{Var})$ such that for all $n \in \mathbb{N}$, there exists $m \in \mathbb{N}$ such that $\boldsymbol{\lambda} \vdash M c_n = c_m$, and for all $d_{S_1}, d_{S_2} \in D$ such that for all $n \in \mathbb{N}$, $\llbracket d_{S_1} c_n \rrbracket = \chi_{S_1}^D(n)$ and $\llbracket d_{S_2} c_n \rrbracket = \chi_{S_2}^D(n)$, we have that for all $n \in \mathbb{N}$, $\llbracket d_{S_2} (M c_n) \rrbracket = \llbracket d_{S_1} c_n \rrbracket$.

## 5 Random Variables

In this section we relate the Boolean-valued Engeler model in $V^A$ from Corollary 34 to the random-variable-based Boolean-valued models of $\lambda$-calculus from [3], and give the example application (Theorem 43).

We start with some terminology. A *negligibility space* $(X, \Sigma, \mathcal{N})$ is a measurable space $(X, \Sigma)$ equipped with a $\sigma$-ideal $\mathcal{N}$ such that $\Sigma / \mathcal{N}$ is a *complete* Boolean algebra, not just $\sigma$-complete. We use $A(X)$ to denote $\Sigma / \mathcal{N}$, as it is the *complete Boolean algebra associated to $X$* or simply the *algebra associated to $X$*.

For a probability space $(X, \Sigma, \mu)$, the *null ideal* $\mathcal{N}(\mu)$ is the $\sigma$-ideal of sets $N \in \Sigma$ with $\mu(N) = 0$, and $\Sigma / \mathcal{N}(\mu)$ is a complete Boolean algebra [13, 322B, 322C], so $(X, \Sigma, \mathcal{N}(\mu))$ is a negligibility space, and $\Sigma / \mathcal{N}(\mu)$ is known as the *measure algebra* of $(X, \Sigma, \mu)$.

Let $Y$ be a countable set. For each $y \in Y$, let $B_y = \{S \subseteq Y \mid y \in S\}$, which form a subbasis of open sets for the positive topology$^{13}$ on $\mathcal{P}(Y)$. All notions of measurability for $\mathcal{P}(Y)$ will be with respect to the Borel $\sigma$-algebra defined by this topology, and since this is a second countable topology, $(B_y)_{y \in Y}$ is also a countable generating set for this $\sigma$-algebra.

▶ **Definition 37.** Let $X = (X, \Sigma_X)$ be a measurable space and $Y$ a countable set. We define $\mathcal{L}^0(X; \mathcal{P}(Y))$ to be the set of measurable functions $X \to \mathcal{P}(Y)$, using the Borel $\sigma$-algebra of the Scott topology of $\mathcal{P}(Y)$. We define a $\Sigma_X$-valued order as follows:

$$
\| a \leq b \|_{\mathcal{L}^0} = \{ x \in X \mid a(x) \subseteq b(x) \}.
$$

The corresponding notion of equality is

$$
\| a = b \|_{\mathcal{L}^0} = \{ x \in X \mid a(x) = b(x) \}.
$$

$^{13}$ The positive topology equals the Scott topology.

<!-- page 13 -->

▶ **Lemma 38.** If $X = (X, \Sigma_X, \mathcal{N}_X)$ is a negligibility space, define $L^0(X; \mathcal{P}(Y))$ to be $\mathcal{L}^0(X; \mathcal{P}(Y))$ modulo the relation $\sim$ defined by: $a \sim b$ iff $X \setminus \|a = b\|_{\mathcal{L}^0} \in \mathcal{N}_X$, which is the usual "almost everywhere" equivalence. Then $\|\leq\|_{L^0}$ and $\| = \|_{L^0}$, defined by composing the corresponding notions for $\mathcal{L}^0(X; \mathcal{P}(Y))$ with $[\cdot] : \Sigma \to A(X)$, are well-defined and make $L^0(X; \mathcal{P}(Y))$ into an $A(X)$-poset.

We define $G_X : L^0(X; \mathcal{P}(Y)) \to \mathcal{P}^{A(X)}(\check{Y})$ as follows, where $a \in \mathcal{L}^0(X; \mathcal{P}(Y))$ and $y \in Y$:

$$G_X([a])(\check{y}) = [a^{-1}(B_y)] = [\{x \in X \mid y \in a(x)\}] \tag{4}$$

The measurability of $a$ guarantees that $a^{-1}(B_y) \in \Sigma$.

▶ **Proposition 39.** For any negligibility space $(X, \Sigma, \mathcal{N})$ and any countable set $Y$, the map $G_X$ is a strict isomorphism of $A(X)$-posets $L^0(X; \mathcal{P}(Y)) \to \mathcal{P}^{A(X)}(\check{Y})$.

Since $\mathcal{P}(E)$ is a reflexive dcpo and has a binary operation $\cdot$ for application, for any measurable space $X$ we can extend this pointwise to $\mathcal{L}^0(X; \mathcal{P}(E))$ by defining for $a, b \in \mathcal{L}^0(X; \mathcal{P}(E))$ and $x \in X$: $(a \cdot b)(x) = a(x) \cdot b(x)$. For a negligibility space $X$ we can then extend this to $L^0(X; \mathcal{P}(E))$ by defining $[a] \cdot [b] = [a \cdot b]$.

▶ **Proposition 40.** Let $(X, \Sigma, \mathcal{N})$ be a negligibility space. Then the above definition of $\cdot : L^0(X; \mathcal{P}(E)) \times L^0(X; \mathcal{P}(E)) \to L^0(X; \mathcal{P}(E))$ is well-defined, and $G_X : L^0(X; \mathcal{P}(E)) \to \mathcal{P}^{A(X)}(\check{E})$ is an "application homomorphism", i.e. for all $[a], [b] \in L^0(X; \mathcal{P}(E))$,

$$G_X([a] \cdot [b]) = G_X([a]) \cdot G_X([b]).$$

We now introduce the following notation. If $S \subseteq E$, define $K_S \in \mathcal{L}^0(X; \mathcal{P}(E))$ to be the function taking the constant value $S$. This relates to $\check{\cdot}$ in the following way.

▶ **Lemma 41.** Let $Y$ be an arbitrary countable set. For all $S \subseteq Y$ we have

$$\|G_X([K_S]) = \check{S}\| = 1$$

Recall that a subbase of clopens for the product topology of $2^\omega$ is given by the sets $(C_{n,b})_{n \in \omega, b \in 2}$, where $C_{n,b} = \{f \in 2^\omega \mid f(n) = b\}$. These sets also generate the Borel $\sigma$-algebra of $2^\omega$.

In the following, we will also have to consider the (isomorphic) product space $2^\omega \times 2^\omega$, but for which we will need to describe the subsets in more detail. So for $i \in \{1, 2\}$, $n \in \omega$ and $b \in 2$ we write $D_{i,n,b} = \{(f_1, f_2) \in 2^\omega \times 2^\omega \mid f_i(n) = b\}$. Then for all $i \in \{1, 2\}$, $n \in \omega$ and $b \in 2$ we have $D_{i,n,b} = \pi_i^{-1}(C_{n,b})$.

Let $X = 2^\omega \times 2^\omega$ equipped with its Borel $\sigma$-algebra as a measurable space. We define $\mu_X$ to be the usual independent fair coin measure, which is to say, it is the unique measure such that for all finitely-supported partial functions $f_1, f_2 : \omega \to 2$

$$\mu\left(\bigcap_{n \in \operatorname{dom}(f_1)} D_{1,n,f_1(n)} \cap \bigcap_{n \in \operatorname{dom}(f_2)} D_{2,n,f_2(n)}\right) = 2^{-(|\operatorname{dom}(f_1)| + |\operatorname{dom}(f_2)|)}.$$

We take the null ideal of this measure as the negligible sets of $X$. Then $\pi_1, \pi_2$ are random variables in $\mathcal{L}^0(X; 2^\omega)$. They define $S_1, S_2 \in \mathcal{P}^{A(X)}(\check{\omega})$ as follows, taking $i \in \{1, 2\}$:

$$S_i(\check{n}) = [\pi_i^{-1}(C_{n,1})] = [D_{i,n,1}]. \tag{5}$$

We remind the reader at this point that $\|\check{n} \in S_i\| = S_i(\check{n})$ because of the way Boolean-valued equality behaves for elements of $\check{\omega}$.

<!-- page 14 -->

**48:14 · Interpreting Lambda Calculus in Domain-Valued Random Variables**

**Proposition 42.** For all $f : \omega \to \omega$, neither $S_1$ nor $S_2$ is the preimage of a finite $A(X)$-subset of $\check{\omega}$, i.e. $\|\exists K \in \mathcal{P}_{\mathrm{fin}}^{A(X)}(\check{\omega}) . \forall n \in \check{\omega} . \check{n} \in S_1 \Leftrightarrow \check{f}(n) \in K\| = 0$, and likewise for $S_2$. Moreover, $\|S_1 = \check{f}^{-1}(S_2)\| = 0$ and $\|S_2 = \check{f}^{-1}(S_1)\| = 0$, i.e. these sets cannot be mapped to each other by any classical function.

**Theorem 43.** There exist sets $T_1, T_2 \subseteq \mathbb{N}$ such that neither can be mapped to the other by a $\lambda$-definable function, i.e. we neither have $T_1 \le_m T_2$ nor $T_2 \le_m T_1$ (recall Proposition 36).

**Proof.** We start by doing Boolean-valued reasoning about $S_1$ and $S_2$, taking $A = A(2^\omega \times 2^\omega)$, and use the fact that the Engeler model $\mathcal{P}^A(\check{E})$ is ($A$-valuedly) a reflexive continuous lattice with numerals (Corollary 34) and Proposition 36.

First, by Theorem 1 applied to Lemma 35 (ii), there exist $d_1, d_2 \in \mathcal{P}^A(\check{E})$ such that for all $n \in \omega$ and $i \in \{1, 2\}$ we have $\|d_i \cdot \check{c}_n = \check{\top}\|^A = \|\check{n} \in S_i\|$ and $\|d_i \cdot \check{c}_n = \check{\bot}\|^A = \neg\|\check{n} \in S_i\|$.

Suppose $M \in \Lambda(\mathrm{Var})$ such that for all $n \in \omega$, there exists $m \in \omega$ such that $\boldsymbol{\lambda} \vdash M c_n = c_m$. In particular, there exists some function $f : \omega \to \omega$ such that for all $n \in \omega$, $\boldsymbol{\lambda} \vdash M c_n = c_{f(n)}$.

Now we consider $\llbracket d_2(\check{M}\check{c}_n)\rrbracket^A$ and $\llbracket d_1\check{c}_n\rrbracket^A$. In the following, for ease of notation, we write an equals sign to mean the corresponding $A$-valued equality being equal to 1:

$$
\llbracket d_2(\check{M}\check{c}_n)\rrbracket^A = d_2 \cdot \llbracket \check{M}\check{c}_n\rrbracket^A = d_2 \cdot \llbracket \check{c}_{f(n)}\rrbracket^A
$$

by Theorem 26. Therefore, $\|\llbracket d_2(\check{M}\check{c}_n)\rrbracket^A = \llbracket \check{\top}\rrbracket^A\| = \|d_2 \cdot \llbracket \check{c}_{f(n)}\rrbracket^A = \llbracket \check{\top}\rrbracket^A\| = \|\check{f}(n) \in S_2\|$, and the corresponding negative statement for $\bot$. Likewise, $\|\llbracket d_1\check{c}_n\rrbracket^A = \llbracket \check{\top}\rrbracket^A\| = \|\check{n} \in S_1\|$, and the corresponding statement for $\bot$. So all together, $\|d_2 \cdot \llbracket \check{M}\check{c}_n\rrbracket^A = d_1 \cdot \llbracket \check{c}_n\rrbracket^A\| = \|\check{f}(n) \in S_2 \Leftrightarrow \check{n} \in S_1\|$. It is proved in Proposition 42 that $\|\forall n \in \check{\omega} . \check{f}(n) \in S_2 \Leftrightarrow \check{n} \in S_1\| = 0$, so we can conclude that $\bigwedge_{n \in \omega} \|d_2 \cdot \llbracket \check{M}\check{c}_n\rrbracket^A = d_1 \cdot \llbracket \check{c}_n\rrbracket^A\| = 0$ for all $M \in \Lambda(\mathrm{Var})$ that map numerals to numerals.

Let $a_1, a_2 \in \mathcal{L}^0(X; \mathcal{P}(E))$ s.t. for $i \in \{1, 2\}$ we have $[a_i] = G_X^{-1}(d_i)$. Then, using Proposition 39, Proposition 40, Lemma 31 and Lemma 41, we get:

$$
\begin{aligned}
0 &= \bigwedge_{n \in \omega} \|G_X^{-1}(d_2 \cdot \llbracket \check{M}\check{c}_n\rrbracket^A) = G_X^{-1}(d_1 \cdot \llbracket \check{c}_n\rrbracket^A)\|_{L^0} \\
&= \bigwedge_{n \in \omega} \|G_X^{-1}(d_2) \cdot G_X^{-1}(\llbracket \check{M}\check{c}_n\rrbracket^A) = G_X^{-1}(d_1) \cdot G_X^{-1}(\llbracket \check{c}_n\rrbracket^A)\|_{L^0} \\
&= \bigwedge_{n \in \omega} \|[a_2] \cdot G_X^{-1}(\llbracket \check{M}\check{c}_n\rrbracket) = [a_1] \cdot G_X^{-1}(\llbracket \check{c}_n\rrbracket)\|_{L^0} \\
&= \bigwedge_{n \in \omega} \|[a_2] \cdot [K_{\llbracket M c_n\rrbracket}] = [a_1] \cdot [K_{\llbracket c_n\rrbracket}]\|_{L^0} \\
&= \left[\bigcap_{n \in \omega} \{x \in X \mid a_2(x) \cdot K_{\llbracket M c_n\rrbracket}(x) = a_1(x) \cdot K_{\llbracket c_n\rrbracket}(x)\}\right] \\
&= [\{x \in X \mid \forall n \in \omega . a_2(x) \cdot \llbracket M c_n\rrbracket = a_1(x) \cdot \llbracket c_n\rrbracket\}],
\end{aligned}
$$

so the set inside the square brackets has measure zero.

Since the set of $M \in \Lambda(\mathrm{Var})$ that map numerals to numerals is countable (because $\mathrm{Var}$ is countable), the set of $x \in X$ such that for all $M \in \Lambda(\mathrm{Var})$ mapping numerals to numerals we have $a_2(x) \cdot \llbracket M c_n\rrbracket \neq a_1(x) \cdot \llbracket c_n\rrbracket$ has measure 1.

For all $i \in \{1, 2\}$, we have, by the definition of $d_i$, for all $n \in \omega$ the statement $\|d_i \cdot \llbracket c_n\rrbracket^A = \llbracket \top\rrbracket^A\| \lor \|d_i \cdot \llbracket c_n\rrbracket^A = \llbracket \bot\rrbracket^A\| = 1$. By a similar argument to that used above, this means that the set of $x \in X$ such that $a_i(x) \cdot \llbracket c_n\rrbracket \in \{\llbracket \top\rrbracket, \llbracket \bot\rrbracket\}$ has measure 1, and by the countability of $\omega$ the set where this is true for both $i \in \{1, 2\}$ and all $n \in \omega$ is also of measure 1.

Therefore the intersection of the sets defined in the previous two paragraphs has measure 1, and so is non-empty and so there exists a point $x$ in it. We can then define $T_i = \{n \in \omega \mid a_i(x) \cdot \llbracket c_n\rrbracket = \llbracket \top\rrbracket\}$, and we have proved, by Proposition 36, that $T_1 \not\le_m T_2$. $\blacktriangleleft$

We could not have done this proof by using the "fact" that $L^0(X; \mathcal{P}(E))$ is a continuous dcpo, because this is not true, as stated in our last proposition.

**Proposition 44.** Let $\mathcal{X} = (X, \Sigma, \mathcal{N})$ be a negligibility space such that $A(X)$ is not atomic, and let $Y$ be a non-empty countable set. Then $L^0(X; \mathcal{P}(Y))$ is not a continuous dcpo.

<!-- page 15 -->

## 6 Conclusions

We have developed domain theory in a Boolean-valued universe of sets. Using the measure algebra as the Boolean algebra we obtained a domain of random variables which can be see to be a reflexive domain *in the internal language of the Boolean-valued set theory*. We have focused on the pure $\lambda$-calculus here but it should be straightforward to extend this to a $\lambda$-calculus with probabilistic choice as an explicit primitive.

There are a number of directions for future work. First, one can use this construction to give semantics to a $\lambda$-calculus extended with probabilistic choice as was done in [3]. In this model it will be interesting to see which equations involving the interplay of choice and the standard $\lambda$-calculus constructions are valid. One could then relate it to an operational semantics as, for example, in [8] but one would need a Boolean-valued notion of operational semantics. More interestingly one could define conditioning as a primitive and explore its semantics. A second line of research is the notion of approximation. A notion of “approximate equality” has been developed recently [22]; the connection to the notion of equality used in the present paper is unclear but there is a similarity in that in both cases equality may only hold partially.

## References

1. Nathanael L. Ackerman, Cameron E. Freer, and Daniel M. Roy. Noncomputable conditional distributions. In *Logic in Computer Science (LICS), 2011 26th Annual IEEE Symposium on*, pages 107–116. IEEE, 2011. doi:10.1109/LICS.2011.49.

2. Nathanael L. Ackerman, Cameron E. Freer, and Daniel M. Roy. On the computability of conditional probability. *J. ACM*, 66(3):23:1–23:40, 2019. doi:10.1145/3321699.

3. Giorgio Bacci, Robert Furber, Dexter Kozen, Radu Mardare, Prakash Panangaden, and Dana Scott. Boolean-valued semantics for the stochastic $\lambda$-calculus. In *Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science*, pages 669–678. ACM, 2018. doi:10.1145/3209108.3209175.

4. Henk P. Barendregt. *The Lambda Calculus: Its Syntax and Semantics*. North-Holland, Amsterdam, 1984.

5. John L. Bell. *Set Theory: Boolean-Valued Models and Independence Proofs*, volume 47 of *Oxford Logic Guides*. Oxford University Press, third edition, 2005.

6. Johannes Borgström, Ugo Dal Lago, Andrew D. Gordon, and Marcin Szymczak. A $\lambda$-calculus foundation for universal probabilistic programming. In Jacques Garrigue, Gabriele Keller, and Eijiro Sumii, editors, *Proceedings of the 21st ACM SIGPLAN International Conference on Functional Programming, ICFP 2016, Nara, Japan, September 18–22, 2016*, pages 33–46. ACM, 2016. doi:10.1145/2951913.2951942.

7. Fredrik Dahlqvist and Dexter Kozen. Semantics of higher-order probabilistic programs with conditioning. *Proc. ACM Program. Lang.*, 4(POPL):57:1–57:29, 2020. doi:10.1145/3371125.

8. Pedro H. Azevedo de Amorim, Dexter Kozen, Radu Mardare, Prakash Panangaden, and Michael Roberts. Universal semantics for the stochastic $\lambda$-calculus. In *Proceedings of the ACM-IEEE Symposium on Logic in Computer Science*, 2021. arXiv preprint:2011.13171.

9. Thomas Ehrhard, Michele Pagani, and Christine Tasson. Measurable cones and stable, measurable functions: a model for probabilistic higher-order programming. *Proceedings of the ACM Symposium on Principles of Programming Languages*, 2(POPL):1–28, 2017. doi:10.1145/3158147.

10. Thomas Ehrhard, Christine Tasson, and Michele Pagani. Probabilistic coherence spaces are fully abstract for probabilistic pcf. In *Proceedings of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages*, pages 309–320, 2014. doi:10.1145/2535838.2535865.

<!-- page 16 -->

**48:16 Interpreting Lambda Calculus in Domain-Valued Random Variables**

11. Erwin Engeler. Algebras and Combinators. *Algebra Universalis*, 13(1):389–392, December 1981. doi:10.1007/BF02483849.

12. Michael P. Fourman and Dana S. Scott. Sheaves and Logic. In Michael Fourman, Christopher Mulvey, and Dana Scott, editors, *Applications of Sheaves: Proceedings of the Research Symposium on Applications of Sheaf Theory to Logic, Algebra, and Analysis, Durham, July 9–21, 1977*, pages 302–401. Springer Berlin Heidelberg, 1979. doi:10.1007/BFb0061824.

13. David H. Fremlin. *Measure Theory*, Volume 3. https://www.essex.ac.uk/maths/people/fremlin/mt.htm, 2002.

14. Gerhard Gierz, Karl H. Hofmann, Klaus Keimel, Jimmie D. Lawson, Michael W. Mislove, and Dana S. Scott. *Continuous Lattices and Domains*, volume 93 of *Encyclopedia of Mathematics and its Applications*. Cambridge University Press, 2003.

15. Robert Goldblatt. *Topoi: The Categorial Analysis of Logic*. Dover, 2006.

16. Noah Goodman, Vikash Mansingkha, Daniel Roy, Keith Bonawitz, and Joshua Tenenbaum. Church: a language for generative models. In *Proceedings of the 24th Conference on Uncertainty in Artificial Intelligence*, pages 220–229, 2008.

17. Chris Heunen, Ohad Kammar, Sam Staton, and Hongseok Yang. A convenient category for higher-order probability theory. In *Proceedings of the Thirty-second Annual ACM-IEEE Symposium on Logic in Computer Science*, pages 1–12, 2017. doi:10.1109/LICS.2017.8005137.

18. Martin Hyland, Misao Nagayama, John Power, and Giuseppe Rosolini. A Category Theoretic Formulation for Engeler-style Models of the Untyped $\lambda$-Calculus. *Electronic Notes in Theoretical Computer Science*, 161:43–57, 2006. Proceedings of the Third Irish Conference on the Mathematical Foundations of Computer Science and Information Technology (MFCSIT 2004). doi:10.1016/j.entcs.2006.04.024.

19. Thomas J. Jech. *Set Theory*. Springer, 3rd Millennium edition, 2003.

20. Stephen C. Kleene and Emil L. Post. The Upper Semi-Lattice of Degrees of Recursive Unsolvability. *Annals of Mathematics*, 59(3):379–407, 1954. doi:10.2307/1969708.

21. Anatoly G. Kusraev and Semën S. Kutateladze. *Boolean Valued Analysis*, volume 494 of *Mathematics and Its Applications*. Springer, 1999. doi:10.1007/978-94-011-4443-8.

22. Radu Mardare, Prakash Panangaden, and Gordon Plotkin. Quantitative algebraic reasoning. In *Proceedings of the 31st Annual ACM-IEEE Symposium on Logic in Computer Science*, pages 700–709, 2016. doi:10.1145/2933575.2934518.

23. Gordon P. Monro. A Category-theoretic Approach to Boolean-valued Models of Set Theory. *Journal of Pure and Applied Algebra*, 42(3):245–274, 1986. doi:10.1016/0022-4049(86)90010-1.

24. Gordon P. Monro. Quasitopoi, Logic and Heyting-valued Models. *Journal of Pure and Applied Algebra*, 42(2):141–164, 1986. doi:10.1016/0022-4049(86)90077-0.

25. Dan Roy. *Computability, inference and modeling in probabilistic programming*. PhD thesis, MIT, June 2011.

26. Dana Scott. A proof of the independence of the continuum hypothesis. *Mathematical Systems Theory*, 1(2):89–111, 1967. doi:10.1007/BF01705520.

27. Dana Scott. Continuous Lattices. In F. William Lawvere, editor, *Toposes, Algebraic Geometry and Logic*, pages 97–136. Springer Berlin Heidelberg, 1972. doi:10.1007/BFb0073967.

28. Dana Scott. Stochastic $\lambda$-calculi. *Journal of Applied Logic*, 12(3):369–376, 2014.

29. Robert I. Soare. *Recursively Enumerable Sets and Degrees*. Perspectives in Mathematical Logic. Springer, 1987.

30. Clifford Spector. Measure-Theoretic Construction of Incomparable Hyperdegrees. *Journal of Symbolic Logic*, 23(3):280–288, September 1958. doi:10.2307/2964288.

31. Sam Staton, Hongseok Yang, Frank Wood, Chris Heunen, and Ohad Kammar. Semantics for probabilistic programming: higher-order functions, continuous distributions, and soft constraints. In *Proceedings of the 31st Annual ACM-IEEE Symposium On Logic In Computer Science*, pages 525–534, 2017.

<!-- page 17 -->

**48:17 · Interpreting Lambda Calculus in Domain-Valued Random Variables**

32. Matthijs Vákár, Ohad Kammar, and Sam Staton. A domain theory for statistical probabilistic programming. *Proceedings of the ACM Conference on Principles of Programming Languages*, 3(POPL):1–29, 2019. doi:10.1145/3290349.

33. Frank Wood, Jan Willem van de Meent, and Vikash Mansinghka. A new approach to probabilistic programming inference. In *Proceedings of the 17th International conference on Artificial Intelligence and Statistics*, pages 1024–1032, 2014. URL: http://proceedings.mlr.press/v33/wood14.html.

## A Appendix

**Proof of Theorem 1.** For (i) and (ii), see [5, Theorem 1.17]; (iii) is a particular instance of what we shall later call the “completeness” of $V^A$ – see [19, Lemma 14.19] or [5, Lemma 1.27]. $\blacktriangleleft$

**Proof of Theorem 26.** It follows from Theorem 1 applied to Definition 25 that there exist some elements of $V^A$ representing functions $\llbracket \cdot \rrbracket^A_\rho$ with the required properties holding with Boolean value 1. So by Corollary 18 we can take $\llbracket \cdot \rrbracket^A_\rho \in \mathbf{Set}_A(\Lambda(D, \check{\mathrm{Var}}, \mathfrak{K})^A, D)$ and also $\llbracket \cdot \rrbracket^A_\rho \in \mathbf{Set}_A(\widecheck{\Lambda(\mathrm{Var})}, D)$ for pure terms (using Proposition 22). So by Definition 16, these define maps in $\mathbf{SetoidR}_A(\Lambda(D, \check{\mathrm{Var}}, \mathfrak{K})^A, D)$ and $\mathbf{SetoidR}_A(\widecheck{\Lambda(\mathrm{Var})}, D)$. So by completeness of $D$, we can apply Definition 13 to get maps in $\mathbf{SetoidF}_A(\Lambda(D, \check{\mathrm{Var}}, \mathfrak{K})^A, D)$ and $\mathbf{SetoidF}_A(\widecheck{\Lambda(\mathrm{Var})}, D)$.

From this, we get that if $\boldsymbol{\lambda} \vdash M = N$, then $\|\widecheck{(M,N)} \in \boldsymbol{\lambda}^A\| = 1$, and therefore for all $\rho$, $\|\llbracket \check{M} \rrbracket_\rho = \llbracket \check{N} \rrbracket_\rho\| = 1$. Since $D$ is strict, this implies that actually $\llbracket \check{M} \rrbracket_\rho = \llbracket \check{N} \rrbracket_\rho$ in the usual sense as well. $\blacktriangleleft$

**Proof of Proposition 28.** We get the first part by applying Theorem 1 to Proposition 27. By Theorem 17, $\mathcal{P}^A(X)$ is complete, and it is clear from its definition that it is total. Now, if $X = \check{Y}$, we use the fact that $\|\widecheck{\mathcal{P}_{\mathrm{fin}}(Y)} = \mathcal{P}^A_{\mathrm{fin}}(\check{Y})\| = 1$ (Proposition 3), so $\widecheck{\mathcal{P}_{\mathrm{fin}}(Y)}$ is also a base for $\mathcal{P}^A(\check{Y})$ with Boolean value 1.

Finally, to show that $\mathcal{P}^A(\check{Y})$ is strict, let $S, T \in \mathcal{P}^A(\check{Y})$ such that $\|S = T\|_{\mathcal{P}^A(\check{Y})} = 1$, which is equivalent to $\|S = T\| = 1$. First observe that $\mathrm{dom}(S) = \mathrm{dom}(\check{Y}) = \mathrm{dom}(T)$, and then that for all $\check{y} \in \mathrm{dom}(\check{Y})$, we have $\|\check{y} \in S\| = S(\check{y})$ and likewise for $T$. Since $\|S = T\| = 1$, for all $y \in Y$ we have

$$S(\check{y}) = \|\check{y} \in S\| = \|\check{y} \in T\| = T(\check{y}),$$

so $S = T$. $\blacktriangleleft$

**Proof of Theorem 30.** By Theorem 2, $\widecheck{(\cdot,\cdot)}$ defines an injective function $\widecheck{\mathcal{P}_{\mathrm{fin}}(E)} \times_A \check{E} = \widecheck{\mathcal{P}_{\mathrm{fin}}(E) \times E} \to \check{E}$. Since $\|\widecheck{\mathcal{P}_{\mathrm{fin}}(E)} = \mathcal{P}^A_{\mathrm{fin}}(\check{E})\| = 1$ by Prop. 3, it also defines an injective function $\mathcal{P}^A_{\mathrm{fin}}(\check{E}) \times_A \check{E} \to \check{E}$. We apply Theorem 1 (i) to Prop. 29 to conclude that $\mathcal{P}^A(\check{E})$ is a reflexive dcpo. $\blacktriangleleft$

**Proof of Corollary 34.** By Lemma 31, $\|\llbracket \check{\bot} \rrbracket^A = \widecheck{\llbracket \bot \rrbracket}\| = 1$, and likewise for $\top$ and the Church numerals.

Then part (i) of Definition 32 is a $\Delta_0$ statement, so it follows by applying Theorem 2 to Proposition 33. Parts (ii)–(iv) then follow by Example 24. $\blacktriangleleft$

<!-- page 18 -->

**48:18 · Interpreting Lambda Calculus in Domain-Valued Random Variables**

**Proof of Lemma 35.**

(i) As Scott topologies are $T_0$, part (i) of Definition 32 implies that there is a Scott-open set $U \subseteq D$ containing one of $\{\llbracket \top \rrbracket, \llbracket \bot \rrbracket\}$ but not the other. We start under the assumption that $\llbracket \top \rrbracket \in U$ and $\llbracket \bot \rrbracket \notin U$. This implies that $\{\llbracket \top \rrbracket\}$ is an open subset of the subspace $\{\llbracket \top \rrbracket, \llbracket \bot \rrbracket\}$.

The map $\mathbf{fun}(\llbracket \neg \rrbracket) : D \to D$ is Scott continuous, and $\mathbf{fun}(\llbracket \neg \rrbracket)(\llbracket \bot \rrbracket) = \llbracket \top \rrbracket$ and vice-versa. So $\mathbf{fun}(\llbracket \neg \rrbracket)^{-1}(U)$ is an open set containing $\llbracket \bot \rrbracket$, but not $\llbracket \top \rrbracket$, proving that $\{\llbracket \bot \rrbracket\}$ is an open subset of the subspace $\{\llbracket \top \rrbracket, \llbracket \bot \rrbracket\}$. This proves that $\{\llbracket \top \rrbracket, \llbracket \bot \rrbracket\}$ is a discrete subspace of $D$, and the proof starting with $\llbracket \bot \rrbracket \in U$ is similar.

To prove the discreteness and distinctness of $\{\llbracket c_n \rrbracket\}_{n \in \mathbb{N}}$, we will need the fact that there exist closed $\lambda$-terms $\mathbf{m}^?$ such that $\boldsymbol{\lambda} \vdash \mathbf{m}^?\, c_n = \top$ if $m = n$ and $\boldsymbol{\lambda} \vdash \mathbf{m}^?\, c_n = \bot$ otherwise. It is not difficult to prove directly that we can take $\mathbf{1}^? = \lambda m.\, \mathbf{if}(\mathbf{0}^?\, m)\, \bot\, (\mathbf{0}^?\, (\mathbf{pred}\, m))$, and $\mathbf{n}^? = \lambda m.\, \mathbf{n{-}1}^?\, (\mathbf{pred}\, m)$. It follows that $\mathbf{fun}(\llbracket \mathbf{n}^? \rrbracket)(\llbracket c_m \rrbracket) = \llbracket \top \rrbracket$ if $n = m$ and $\llbracket \bot \rrbracket$ otherwise.

Now, if $m \neq n$ are elements of $\mathbb{N}$, we have $\boldsymbol{\lambda} \vdash \mathbf{m}^?\, c_m = \top$, and $\boldsymbol{\lambda} \vdash \mathbf{m}^?\, c_n = \bot$, so $\mathbf{fun}(\llbracket \mathbf{m}^? \rrbracket)(\llbracket c_m \rrbracket) = \llbracket \top \rrbracket \neq \llbracket \bot \rrbracket = \mathbf{fun}(\llbracket \mathbf{m}^? \rrbracket)(\llbracket c_n \rrbracket)$. As $\mathbf{fun}(\llbracket \mathbf{m}^? \rrbracket)$ is a function, it follows that $\llbracket c_m \rrbracket \neq \llbracket c_n \rrbracket$.

To prove the discreteness of $\{\llbracket c_n \rrbracket\}_{n \in \mathbb{N}}$, we show that for all $m \in \mathbb{N}$, the singleton $\{\llbracket c_m \rrbracket\}$ is relatively open in $\{\llbracket c_n \rrbracket\}_{n \in \mathbb{N}}$. Let $U \subseteq D$ be a Scott-open set such that $\llbracket \top \rrbracket \in U$, but $\llbracket \bot \rrbracket \notin U$. Then $V = \mathbf{fun}(\llbracket \mathbf{m}^? \rrbracket)^{-1}(U)$ is a Scott-open set such that $\llbracket c_m \rrbracket \in V$ but $\llbracket c_n \rrbracket \notin V$ for all $n \in \mathbb{N}$ such that $n \neq m$.

(ii) Given $A \subseteq \mathbb{N}$, define $g : \{\llbracket c_n \rrbracket\}_{n \in \mathbb{N}} \to D$ by $g(\llbracket c_n \rrbracket) = \chi_A^D(n)$. By the discreteness of $\{\llbracket c_n \rrbracket\}_{n \in \mathbb{N}}$, proved in the previous part, this is continuous. Since $D$ is a continuous lattice, and therefore injective [27, Theorem 2.12], $g$ extends to a Scott-continuous map $\bar{g} : D \to D$, and since $(D, \mathbf{lam}, \mathbf{fun})$ is a reflexive dcpo we can define $d_g = \mathbf{lam}\bar{g}$, and then for all $n \in \mathbb{N}$:

$$
d_g \cdot \llbracket c_n \rrbracket = \bar{g}(\llbracket c_n \rrbracket) = \chi_A^D(n). \quad \blacktriangleleft
$$

**Proof of Lemma 38.** We prove that $\|a \leq b\|_{\mathcal{L}^0}$ is measurable as follows. First, define $\gamma \subseteq \mathcal{P}(Y) \times \mathcal{P}(Y)$ to be the graph of the $\subseteq$ relation, i.e. $\gamma = \{(S, T) \in \mathcal{P}(Y) \times \mathcal{P}(Y) \mid S \subseteq T\}$. $\|a \leq b\|_{\mathcal{L}^0} = \langle a, b \rangle^{-1}(\gamma)$, so since $\langle a, b \rangle : X \to \mathcal{P}(Y) \times \mathcal{P}(Y)$ is measurable, we only need to show that $\gamma$ is measurable with respect to the product measurable space structure. We have

$$
\begin{aligned}
\gamma &= \{(S, T) \in \mathcal{P}(Y) \times \mathcal{P}(Y) \mid \forall y \in Y.\, y \in S \Rightarrow y \in T\} \\
&= \bigcap_{y \in Y} \{(S, T) \in \mathcal{P}(Y) \times \mathcal{P}(Y) \mid y \notin S \text{ or } y \in T\} \\
&= \bigcap_{y \in Y} \bigl(\{(S, T) \in \mathcal{P}(Y) \times \mathcal{P}(Y) \mid y \notin S\} \cup \{(S, T) \in \mathcal{P}(Y) \times \mathcal{P}(Y) \mid y \in T\}\bigr) \\
&= \bigcap_{y \in Y} \bigl((\mathcal{P}(Y) \setminus B_y) \times \mathcal{P}(Y)\bigr) \cup (\mathcal{P}(Y) \times B_y).
\end{aligned}
$$

Measurability then follows from the countability of $Y$. For the well-definedness of $\|\leq\|_{L^0}$, it is clear that if $a \sim a'$ and $b \sim b'$, then $\|a \leq b\|_{\mathcal{L}^0}$ and $\|a' \leq b'\|_{\mathcal{L}^0}$ can only differ where $a$ differs from $a'$ or $b$ differs from $b'$, and the set of all such points is in $\mathcal{N}_X$. It is easy to deduce the transitivity (in the sense of Definition 11 (i)) from transitivity of $\subseteq$, and part (ii) of the definition of an $A(X)$-poset follows because $\|a \leq a\|_{L^0} = 1$ for all $a \in L^0(X; \mathcal{P}(Y))$. $\blacktriangleleft$

<!-- page 19 -->

**Proof of Proposition 39.** We show that for all $a, b \in \mathcal{L}^0(X; \mathcal{P}(Y))$, $\|G_X([a]) \leq G_X([b])\|_{\mathcal{P}^{A(X)}(\check{Y})} = \|[a] \leq [b]\|_{L^0}$. This shows, in one go, that $G_X$ is an $A(X)$-monotone function and also injective (using the fact that $L^0(X; \mathcal{P}(Y))$ is total, i.e. $\varepsilon_{L^0(X; \mathcal{P}(Y))}([a]) = [X]$ for all $a \in \mathcal{L}^0(X; \mathcal{P}(Y))$).

We start by expanding the definitions:

$$
\begin{aligned}
\|G_X([a]) \leq G_X([b])\|_{\mathcal{P}^{A(X)}(\check{Y})} &= \|G_X([a]) \subseteq G_X([b])\| \\
&= \bigwedge_{t \in \mathrm{dom}(G_X([a]))} \|t \in G_X([a]) \Rightarrow t \in G_X([b])\| = \bigwedge_{y \in Y} G_X([a])(\check{y}) \Rightarrow G_X([b])(\check{y}) \\
&= \bigwedge_{y \in Y} [\{x \in X \mid y \in a(x)\} \Rightarrow \{x \in X \mid y \in b(x)\}] \\
&= \left[\bigcap_{y \in Y} \{x \in X \mid y \in a(x) \text{ implies } y \in b(x)\}\right] \\
&= [\{x \in X \mid \forall y \in Y.\, y \in a(x) \text{ implies } y \in b(x)\}] \\
&= [\{x \in X \mid a(x) \subseteq b(x)\}] = \|[a] \leq [b]\|_{L^0}.
\end{aligned}
$$

Since $L^0(X; \mathcal{P}(Y))$ is a strict $A(X)$-setoid, and $\mathcal{P}^{A(X)}(\check{Y})$ is total, implying that $G_X$ is an injective function. So to prove that $G_X$ is a strict isomorphism, we only need to show that $G_X$ is surjective.

Let $b \in \mathcal{P}^{A(X)}(\check{Y})$. For each $y \in Y$, pick $S_y \in \Sigma$ such that $[S_y] = b(\check{y})$. Define a function $a : X \to \mathcal{P}(Y)$ by $a(x) = \{y \in Y \mid x \in S_y\}$. For each $y \in Y$, we have

$$
a^{-1}(B_y) = \{x \in X \mid a(x) \in B_y\} = \{x \in X \mid y \in a(x)\} = \{x \in X \mid x \in S_y\} = S_y \in \Sigma.
$$

Since $(B_y)_{y \in Y}$ generates the Borel $\sigma$-algebra of $\mathcal{P}(Y)$, this implies that $a$ is measurable. For all $y \in Y$, we then have

$$
G_X([a])(\check{y}) = [a^{-1}(B_y)] = [S_y] = b(\check{y}),
$$

and therefore $G_X([a]) = b$, as required to prove $G_X$ surjective. $\blacktriangleleft$

**Proof of Proposition 40.** In fact, we will prove the first part by deducing it from the second part. So let $a, b \in \mathcal{L}^0(X; \mathcal{P}(E))$. Then for all $q \in E$ we have

$$
\begin{aligned}
(G_X([a]) \cdot G_X([b]))(\check{q})
&= \|\exists K \in \mathcal{P}_{\mathrm{fin}}^{A(X)}(\check{E}).\, K \subseteq G_X([b]) \text{ and } (K, \check{q})^{A(X)} \in G_X([a])\| \\
&= \|\exists K \in \mathcal{P}_{\mathrm{fin}}(E).\, K \subseteq G_X([b]) \text{ and } (K, \check{q})^{A(X)} \in G_X([a])\| && \text{Proposition 3} \\
&= \bigvee_{K \in \mathcal{P}_{\mathrm{fin}}(E)} \|\check{K} \subseteq G_X([b])\| \wedge \|\widecheck{(K, q)} \in G_X([a])\| \\
&= \bigvee_{K \in \mathcal{P}_{\mathrm{fin}}(E)} G_X([a])(\widecheck{(K, q)}) \wedge \bigwedge_{k \in K} G_X([b])(\check{k}) \\
&= \bigvee_{K \in \mathcal{P}_{\mathrm{fin}}(E)} [\{x \in X \mid (K, q) \in a(x)\}] \wedge \bigwedge_{k \in K} [\{x \in X \mid k \in b(x)\}] \\
&= \bigvee_{K \in \mathcal{P}_{\mathrm{fin}}(E)} [\{x \in X \mid (K, q) \in a(x)\}] \wedge [\{x \in X \mid K \subseteq b(x)\}] \\
&= [\{x \in X \mid \exists K \in \mathcal{P}_{\mathrm{fin}}(E).\, K \subseteq b(x) \text{ and } (K, q) \in a(x)\}] && \text{as } \mathcal{P}_{\mathrm{fin}}(E) \text{ countable} \\
&= [\{x \in X \mid q \in a(x) \cdot b(x)\}] \\
&= G_X([a \cdot b])(\check{q}),
\end{aligned}
$$

<!-- page 20 -->

**48:20 · Interpreting Lambda Calculus in Domain-Valued Random Variables**

so all together we have proved that $G_X([a]) \cdot G_X([b]) = G_X([a \cdot b])$. In passing, we have proved that for all $q \in E$, $(a \cdot b)^{-1}(B_q)$ is measurable, and therefore that $a \cdot b \in \mathcal{L}^0(X; \mathcal{P}(E))$.

If $a', b' \in \mathcal{L}^0(X; \mathcal{P}(E))$ such that $[a'] = [a]$ and $[b'] = [b]$, then by Proposition 39 and the fact that $\mathcal{P}^{A(X)}(\check{E})$ is a strict $A(X)$-setoid:

$$
G_X([a \cdot b]) = G_X([a]) \cdot G_X([b]) = G_X([a']) \cdot G_X([b']) = G_X([a' \cdot b']),
$$

and therefore $[a \cdot b] = [a' \cdot b']$, so the definition $[a] \cdot [b] = [a \cdot b]$ genuinely defines a function $L^0(X; \mathcal{P}(E)) \times L^0(X; \mathcal{P}(E)) \to L^0(X; \mathcal{P}(E))$. Putting this together with what we proved above gives us $G_X([a]) \cdot G_X([b]) = G_X([a] \cdot [b])$. $\blacktriangleleft$

**Proof of Lemma 41.** It suffices to show that for all $y \in Y$, $\|\check{y} \in G_X([K_S])\| = \|\check{y} \in \check{S}\|$. We have

$$
\|\check{y} \in G_X([K_S])\| = G_X([K_S])(\check{y}) = [\{x \in X \mid y \in K_S(x)\}] = [\{x \in X \mid y \in S\}] = \|\check{y} \in \check{S}\|.
$$

$\blacktriangleleft$

**Proof of Proposition 44.** First, let $p = \bigvee \{a \in A(X) \mid a \text{ an atom}\}$. As $A(X)$ is not atomic, $\neg p \neq 0$, so there is a set $S \in \Sigma$ such that $S \notin \mathcal{N}$ and $[S] = \neg p$. By definition there are no atoms below $[S]$. Define

$$
b(x) = \begin{cases} Y & \text{if } x \in S \\ \emptyset & \text{otherwise,} \end{cases}
$$

where $x \in X$. This defines a measurable function $X \to \mathcal{P}(Y)$. As $S \notin \mathcal{N}$, $[b] \neq [K_\emptyset]$. We show that $L^0(X; \mathcal{P}(Y))$ is not continuous by showing that $[b]$ is not the supremum of elements way below it, which will follow from the fact that the only element of $L^0(X; \mathcal{P}(Y))$ that is way below $[b]$ is $[K_\emptyset]$.

If the only element below $[b]$ is $[K_\emptyset]$, then we are finished, so we reduce to the case that there is at least one $[a] \in L^0(X; \mathcal{P}(Y))$ such that $[K_\emptyset] < [a] < [b]$. Define $T = a^{-1}(\mathcal{P}(Y) \setminus \{\emptyset\})$, which is in $\Sigma$ because $a$ is measurable and $\mathcal{P}(Y) \setminus \{\emptyset\} = \bigcup_{y \in Y} B_y$ and is therefore a Borel set. We have $T \setminus S \in \mathcal{N}$, so we redefine $T$ to be $T \cap S$ if necessary to make $T \subseteq S$.

Since there are no atoms below $[S]$, there are none below $[T]$ either, so there exists a non-zero element $a_1 \in A(X)$ such that $a_1 \leq [T]$ and $a_1$ has no atoms below it. We can repeat this argument to form a strictly descending sequence $(a_i)_{i \in \mathbb{N}}$ where for all $i \in \mathbb{N}$, $a_i$ has no atoms below it and $a_i \leq [T]$. We can define $b_i = a_i \setminus \bigwedge_{i=1}^\infty a_i$, to get such a strictly decreasing sequence $(b_i)_{i \in \mathbb{N}}$, now with $\bigwedge_{i=1}^\infty b_i = 0$. Since $A(X) = \Sigma / \mathcal{N}$, we can find a sequence $(V_i)_{i \in \mathbb{N}}$ of elements of $\Sigma$ such that for all $i \in \mathbb{N}$, $[V_i] = b_i$, and by adjusting negligible sets it can be arranged that $(V_i)_{i \in \mathbb{N}}$ is also strictly descending. Defining $T_i = T \setminus V_i$, then $(T_i)_{i \in \mathbb{N}}$ is strictly increasing with respect to $\subseteq$, maps to a strictly increasing sequence under $[-]$, and $T \setminus \bigcup_{i=1}^\infty T_i \in \mathcal{N}$. Define, for each $i \in \mathbb{N}$, $c_i : X \to \mathcal{P}(Y)$ as follows:

$$
c_i(x) = \begin{cases} Y & \text{if } x \in T_i \cup S \setminus T \\ \emptyset & \text{if } x \in T \setminus T_i \cup X \setminus S, \end{cases}
$$

where $x \in X$. Each $c_i$ is measurable for the same reasons that $b$ is, and $([c_i])_{i \in \mathbb{N}}$ is a strictly increasing sequence in $L^0(X; \mathcal{P}(Y))$. Since for all $i \in \mathbb{N}$, $c_i(x) = \emptyset$ for all $x \in T \setminus T_i$ and $T \setminus T_i \notin \mathcal{N}$, while $a(x) \neq \emptyset$ for all $x \in T \supseteq T \setminus T_i$, we have $[a] \not\leq [c_i]$. But $\bigvee_{i=1}^\infty [c_i] = [\bigvee_{i=1}^\infty c_i] = [b]$ because $T \setminus \bigcup_{i=1}^\infty T_i \in \mathcal{N}$. Therefore $a$ is not way below $b$. $\blacktriangleleft$
