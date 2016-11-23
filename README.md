Lambda coinduction is explained in _Generalised Coinduction_ by Falk Bartels (2003)

This library allows provides a EDSL that captures a class of
productive coinductive functions in Haskell. The type-system
ensures the productivity of the definitions.

The scheme of definition is called lambda coinduction by Falk
Bartels.  It generalises the guardedness criteria, by
allowing _causal_ functions under a constructor guard and
above a recursive call.

The adjective _causal_ is borrowed from the field of stream
programming where a causal stream function preserve a
causality property: the output at time 't' may only depend on
inputs at times less or equal to 't'. If a function is
_strictly causal_, it's output depends on strictly earlier
inputs. _strictly causal_ functions are also called
_contractions_ and their fixed-point is necessarily
productive.  In the context of coinductive function,
causality is expressed in terms of the prefixes of the
datastructures being consumed and produced: for a causal
function, any prefix of its output only depend on input
prefixes at most as deep. And strictly causal functions
ensure that the output prefix depends only on strictly less
deep prefixes of inputs.

At the core of the library lies an interesting mechanism: The
class `IsCausal` defines a method over a type `Term` which is
the free monad over the functor `Causal` which is an
existential type capturing all the functors that are instance
of `IsCausal`.

I wrote four versions of the library by increasing order of
generality: `Causal` works on types of kind `*`,
`CausalParam` works on types of kind `* -> *` and
`CausalCategoricalPolymorphism` works on types of any kind.
Finally, `UCausal` works over the universe of all coinductive
types, allowing the definition of functions whose domain and
range have different types. `UCausal` is the most general and
practical implementation.

`ModularDatatypes`
generalises the central mechanism of `Causal`, thus
illustrating a new way to write modular datatypes a la
carte, different from Swierstra's idea.

`ModularDatatypes.Existential` is a first version with some
limitations that the second version
`ModularDatatypes.Subtyping` addresses.
