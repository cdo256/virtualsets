{ inputs, ... }:
{
  perSystem =
    { system, pkgs, ... }:
    {
      config.packages = rec {
        agda-base = inputs.onelab.packages.${system}.agda;
        agda = inputs.agda-cubical.packages.${system}.agdaWithCubical;
        just-agda = inputs.just-agda.packages.${system}.default.override {
          inherit agda;
          inherit (pkgs.emacsPackages) agda2-mode;
        };
      };
    };
}
