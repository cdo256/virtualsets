{ ... }:
pkgs: super:
let
  thunkSource = (import ./dep/nix-thunk { inherit pkgs; }).thunkSource;
in
{
  # Can't just override all Haskell packages because callCabal2nix
  # somehow depends on mime-types
  labHaskellPackages = super.haskell.packages.ghc947.override (old: {
    overrides = self: hsuper: {
      Agda =
        pkgs.haskell.lib.overrideCabal
          (self.callCabal2nixWithOptions "Agda" (thunkSource ./dep/Agda) "-f optimise-heavily -f debug" { })
          {
            enableSeparateBinOutput = true;
            doCheck = false;
            doHaddock = false;
            testHaskellDepends = [ ];
            enableExecutableProfiling = false;
            enableLibraryProfiling = false;
          };
    };
  });
}
