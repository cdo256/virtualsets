{ inputs, ... }:
{
  perSystem =
    { system, pkgs, ... }:
    {
      config.packages = rec {
        agda-base = pkgs.agda;
        agda = agda-base.withPackages (ps: [
          ps.standard-library
          ps.cubical
        ]);
        just-agda = inputs.just-agda.packages.${system}.default.override {
          inherit agda;
          inherit (pkgs.emacsPackages) agda2-mode;
        };
      };
    };
}
