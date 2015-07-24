Lambda coinduction is explained in _Generalised Coinduction_ by Falk Bartels (2003)

This library allows us to write lambda coinductive
definitions. Programs that typecheck are automatically
productive!  Lambda coinduction generalises the guardedness
criteria, by allowing _causal_ functions under a constructor
guard and above a recursive call.

At the core of the library lies an interesting mechanism: The
class `IsCausal` defines a method over a type `Term` which is
the free monad over the functor `Causal` which is an
existential type capturing all the functors that are instance
of `IsCausal`.

I wrote three versions of the library by increasing order of
generality: `Causal` works on types of kind `*`,
`CausalParam` works on types of kind `* -> *` and
`CausalCategoricalPolymorphism` works on types of any kind.

`ModularDatatypes`
generalises the central mechanism of `Causal`, thus
illustrating a new way to write modular datatypes a la
carte, different from Swierstra's idea.

`ModularDatatypes.Existential` is a first version with some
limitations that the second version
`ModularDatatypes.Subtyping` addresses.
