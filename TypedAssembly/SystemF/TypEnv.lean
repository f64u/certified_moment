import «TypedAssembly».SystemF.Typ

abbrev TypEnv n := List (Typ n)

abbrev liftTE d (te : TypEnv n) := List.map (liftTT d) te

abbrev substTE d (u : Typ (n + 1)) (te : TypEnv (n + 1)) := List.map (substTT d u) te
