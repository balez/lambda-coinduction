Extended_Guardedness_Examples.hs
  :  Illustrates lambda coinduction.

Causal.lhs
  :  Extended guardedness recursion by
     syntactic coalgebras in a compositional way

CausalParam.lhs
  :  Support for parametric datatypes like streams, the
     implementation is virtually identical to Causal.lhs, by
     using a categorical lifting.

CausalCategoricalPolymorphism.lhs
  :  Generalisation of both `Causal` and `CausalParam` to work
     on any category using `PolyKinds` extension.

MixedDatatypes.lhs
  : Generalises `Causal' and `CausalParam' to work with
    coinductive functions with different types.

UCausal.lhs
  : More specific implementation of the concepts introduced
    in `MixedDatatypes`. Can be used for functions on mixed
    datatypes with parametricity. Fixed-points of
    contractions.

Contractions.lhs
  :  Fixed-points of contractions using G.Hutton and
     M.Jaskelioff encoding.
