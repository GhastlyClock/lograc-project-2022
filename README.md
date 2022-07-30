# Definitional Interpreter - Exceptions and state

This repository contains the project for course Logic in computer science from Faculty of Mathematic and Physics, Universiy of Ljubljana, year 2022.

Goal of the project was to define a (monadic) definitional interpreter for the fine-grained call-by-value $\lambda$-calculus and extend computaions/procedures with additional operations:
* for exceptions, operation $raise \ e$, where $e$ is some exception.
* for state, two operations $get \ (x.M)$ and $put \ V \ M$, where $get$ binds a variable of a base type of state values, and where $put$ takes as argument a value $V$ of this base type.

We also had to define equational theory and prove soundness.

# Theory
## Fine-grained call-by-value $\lambda$-calculus with exceptions and state

Types: 
    $$A, B ::= unit \ | \ A \rightarrow B \ | \ TState$$
Context: 
    $$\Gamma ::= x_1 : A_1 ,\ldots, x_n : A_n$$
Values: 
    $$V ::= var \ | \ * \ | \ \lambda \ | \ const$$
Computations: 
$$M, N ::= return \ V \ | \ let \   x = M \ in \ N \  | \ app \ M \ N | \ raise \ e \ | \ get \ x.M \ | \ put \ V \ M $$
Judgements:
$$\Gamma \vdash^{v} V : A, \ \ \ \ \ \ \ \Gamma \vdash^{c} M : A $$

## Denotational semantics

For every type $A$ let's define set $[[ \  A \ ]] $:
$$[[ \  unit \ ]]  = \{tt\}, \quad [[ \  A \to B \ ]]  = T [[ \  B \ ]] ^{[[ \  A \ ]] }, \quad [[ \  TState \ ]]  = \mathbb{S}$$

We define interpretation of context as follows:
$$[[ \  \Gamma \ ]]  = [[ \  x_1 : A_1, \ldots, x_n : A_n \ ]]  = [[ \  A_1 \ ]]  \times \cdots \times [[ \  A_n \ ]]$$

## Denotational semantics - values

Denotational semantics of values is defined as function: $$[[ \  \Gamma \vdash^v V : A \ ]]  : [[ \  \Gamma \ ]]  \to [[ \  A \ ]] ,$$
where:
* $[[ \  x_1 : A_1, \ldots, x_n : A_n \vdash^v var \ x_i : A_i \ ]]  (a_1, \ldots, a_m) = a_i$
* $[[ \  \Gamma \vdash^v \lambda x.M : A \to B \ ]]  (\gamma) = a \in [[ \  A \ ]]  \mapsto [[ \  \Gamma, x : A \vdash^c M : B \ ]]  (\gamma , a)$
* $[[ \  \Gamma \vdash^v const \ s : A \ ]]  (\gamma) = s $
* $[[ \  \Gamma \vdash^v \star : unit  \ ]]  (\gamma) = tt$

## Monad

* Program with computational effects (exceptions and state).
* We define 2 universal sets : $\mathbb{E}$ - $\text{exceptions}$, $\mathbb{S}$ - $\text{states}$.
* We fix a monad ($T$, $\eta$, $\gg=$) on a Set, where
$$T \ X \ = \ \mathbb{S} \rightarrow \ \mathbb{E} \ + \ (\mathbb{S} \ \times \ X)$$
* We define functions:
  * $raise' : \mathbb{E} \rightarrow  T X$
  * $get' : (\mathbb{S} \rightarrow T A) \rightarrow T X$
  * $put' : \mathbb{S} \rightarrow T X \rightarrow T X$

## Denotational semantics - computations


Denotational semantics of computations is defined as function $$[[ \  \Gamma \vdash^c M : A \ ]]  : [[ \  \Gamma \ ]]  \to T [[ \  A \ ]] ,$$
where:
* $[[ \  \Gamma \vdash^c return \ V : A \ ]]  (\gamma) = \eta \ ([[ \  \Gamma \vdash^v V : A \ ]]  (\gamma)) $
* $[[ \  \Gamma \vdash^c let\ x = M \ in \ N  : A \to B \ ]]  (\gamma) = [[ \  \Gamma \vdash^c M : A \ ]] (\gamma)  \gg= (y \in TState \mapsto ( x \in [[ \ A \ ]] \mapsto [[ \  \Gamma \vdash^c N : B \ ]] (\gamma, x) ) \ y )  $
* $[[ \  \Gamma \vdash^c app \ M \ N : B \ ]]  (\gamma) = ([[ \  \Gamma \vdash^c M : A \to B \ ]]  (\gamma)) \ ([[ \  \Gamma \vdash^c N : A \ ]]  (\gamma))$
* $[[ \  \Gamma \vdash^c get \ x.M : A \ ]]  (\gamma) = get' (\lambda s \to [[ \  \Gamma, x : TState \vdash^c M : A \ ]]  (\gamma, s)) $
* $[[ \  \Gamma \vdash^c put \ V \ M : A \ ]]  (\gamma) =  put' \ ([[ \  \Gamma \vdash^v V : TState \ ]]  (\mu)) \ ([[ \  \Gamma \vdash^c M : A \ ]]  (\gamma))$
* $[[ \  \Gamma \vdash^c raise \ e : A \ ]]  (\gamma) = raise' \ e $

## Equtional theory

We say that terms $\Gamma \vdash e : A$ and $\Gamma \vdash e' : A$ are denotionally equivalent if their interpretations are equal $$[[ \  \Gamma \vdash e : A \ ]]  = [[ \  \Gamma \vdash e' : A \ ]] .$$ 
We denote this with $\Gamma \vdash e \equiv e' : A$ or $e \equiv e'$.

Equations:
* $\lambda x.(app \ V \ x) \equiv V $
* $app \ (\lambda x.M) \ V \equiv M [V/x] $
* $let \ (x = M) \ in \ (return \ var \ x) \equiv M $
* $let \ (x = return \ V) \ in \ M \equiv M [V/x] $
* $let \ x = (y = \ let \ M_1 \ in \ M_2) \ in \ M_3 \equiv \ let \ x = M_1  \ in \ (let \ y = M_2 \ in \ M_3) $
* $let \ x = (y = \ put \ V \ M_1) \ in \ M_2 \equiv \ put \ V \ (let \ (x = M_1) \ in \  M_2) $
* $let \ (x = \ get \ y.M_1) \ in \ M_2 \equiv \ get \ x.(let \ (y = M_1) \ in \ M_2) $
* $put \ V \ (get \ x.M) \equiv \ put \ V \ (M [V/x]) $
* $get \ M \equiv M $
* $put \ V_1 \ (put \ V_2 \ M) \equiv \ put \ V_2 \ M $
* $put \ V \ (raise\ e) \equiv \ raise \ e $
* $get \ x.(raise \ e) \equiv \ raise \ e $
* $let \ (x = \ raise \ e) \ in \ M \equiv \ raise \ e $


## Soundness

The interpretation of the fine-grain call-by-value calculus with monad $M$ is sound:
1. if $\Gamma \vdash^v V \equiv U : A$ then $[[ \  V \ ]] ^v = [[ \  W \ ]] ^v : [[ \  \Gamma \ ]]  \to [[ \  A \ ]]$ and
2. if $\Gamma \vdash^c M \equiv N : A$ then $[[ \  M \ ]] ^c = [[ \  N \ ]] ^c : [[ \  \Gamma \ ]]  \to T [[ \  A \ ]]$

where $T$ is carrier of monad $M$.
