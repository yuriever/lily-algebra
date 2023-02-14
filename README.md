# Package ``lily`algebra` ``

A Mathematica package for implementing and managing finitely presented associative algebras.

The documentation can also be found on [my website](https://yuriever.github.io/symbolic/package-lily-algebra/).

* Dependency: 
    
    * ``lily`class` ``

* Object:

    * class: `"(compounded) algebra"`

    * instance: `"algebra"`

    * member: `"operator", "relation", "printing"`

## Methods

* `algebraDefine[algList_|alg_]` - define and initiate algebras.

    * `algebraDefineQ[alg_]` - check whether an algebra is defined.

    * `algebraDefineInternal[]` - define the internal algebras, including `"conjugate", "tensorProduct", "comultiplication"`.

* `algebraDefault[algList_|alg_]` - set default algebras to build the compounded algebra.

* `algebraReset|algebraUnset[algList_|alg_]` - reset/unset the algebras.

* `algebraAdd|algebraDelete[algList_|alg_,assoc_]` - add to/delete from the algebras. The operator form is supported but without string auto-completion. The argument `assoc_` accepts `_Rule|{___Rule}|_Association`. For example, the CCR can be added as,

    ``` wl
    algebraDefine["CCR"];
    <|"operator"->{x,p},"relation"->{x**p:>p**x+1}|>//algebraAdd["CCR"]
    ```

* `algebraShow[alg_]` - show the algebra.

* `operator|relation|printing[alg_]` - return the members of the algebra.

<h3 class="nocount">Some shortcuts</h3>

* `operator|relation|printing[]` - return the members of the default algebras.

* `algebraDefine[]` - return the list of defined algebras;

* `algebraDefault[]` - return the list of default algebras;

* `algebraReset|algebraUnset[]` - reset/unset the default except internal algebras.

* `algebraReset|algebraUnset[All]` - reset/unset all the defined except internal algebras.

* `algebraShow[]` - show the default algebras.

## Functionalities

### Pre-defined internal algebras

* `algebraInternal[_]` - private symbol storing the internal algebras.

| Name  | System operator occupation    | Meaning   |
| :-    | :-                            | :-        |
| `"multiplication"`   | `NonCommutativeMultiply` | associativity, linearity over $\C$ |
| `"tensorProduct"`    | `CircleTimes`            | strict tensor category with identity `id` |
| `"conjugate"`        | `SuperDagger`            | dagger structure |
| `"comultiplication"` | `CircleTimes`            | coassociativity (**TODO**) |

### Questing functions 

* `scalarQ|operatorQ[_]` - check whether the expression is C-number/Q-number by the default algebra.

* `generatorQ[op_Symbol|op_Symbol[___]]` - check whether the symbol is a generator the default algebra.

### Algebra simplification

* `algebraSimplify[_]` - simplify the expression by the default algebra.

* `algebraPrint[_]` - format the expression by the default algebra.

* `algebraEquation[_]` - return a formatted equation with the input at RHS and the simplified one at LHS.

Table of shortcuts:

| Name                  | Meaning |
| :-                    | :- |
| `algS[_]`        | `algebraSimplify` |
| `algP[_]`        | `algebraPrint` |
| `algSP[_]`       | `algebraSimplify + algebraPrint` |
| `algSS[_]`       | `algebraSimplify + FullSimplify` |
| `algSSP[_]`      | `algebraSimplify + algebraPrint + FullSimplify` |
| `algE[_]`        | `algebraEquation` |
| `algES[_]`       | `algebraEquation + FullSimplify` |
| `algEqualQ[_,_]` | `algebraSimplify + Equal` |
| `algSameQ[_,_]`  | `algebraSimplify + SameQ` |

### Commutator, adjoint and power

* `comm[_,__]` - (n-)commutator.

    * `anticomm[_,__]` - (n-)anti-commutator.

    * `jacobiIdentity[_,_,_]` - the Jacobi identity.

* `commSim|anticommSim[_,__]` - simplify the (anti-)commutator.


* `commDefine[_,_]:>_` - define commutation relations with condition, order-reversing and anti-commutator. For example, the CCR can be packed into 

    ``` wl
    commDefine[x,p]:>1
    commDefine[x,p,"reverse"]:>1/;True
    ```

    ``` wl
    Out[]= x**p:>1+p**x
    Out[]= p**x:>-1+x**p/;True
    ```    

* `operatorPower[op_,order_:1]` - power of operators, $x^n$.

    * `operatorExp[op_,orderMax_,parameter_:1]` - exponential of operators upto the max order $n$, $[e^{t x}]_n=\sum_{i=0}^{n}\frac{t^i}{i!} x^i$.

* `adjoint[op_,order_:1][expr_]` - the adjoint action of Lie algebra, $\ad^n_x\cdot y$.

    * `adjointExp[op_,orderMax_,parameter_:1][expr_]` - the adjoint action of Lie group upto the max order $n$, $[\Ad_{x}(t)]_n\cdot y=[e^{t x}]_n\, y\, [e^{-t x}]_n$.

### Inner product

This functionality needs the algebra `"conjugate"`.

* `innerProduct[_,_]` - inner product of two vectors. For operators $x,y$ this gives $x^{\dagger}\cdot y$.

### Tensor product

This functionality needs the algebra `"tensorProduct"`.

* `id` - identity of tensor product.

* `tensorRankSet[op_|{ops__},rank_]` - set the tensor rank of generators with respect to tensor product.

* `tensorRank[op_]` - return the tensor rank of generators.

* `tensorThread` - composite tensors over multiplication according to tensorRank. 

### Scalar extraction

* `scalarSeparate|scalarExtract[__]` - separate scalars and operators in the expressions.

## To-do list and other issues

* TODO: implement the comultiplication.