{ self, inputs, ... }:
{
  perSystem =
    {
      system,
      pkgs,
      lib,
      ...
    }:
    {
      options.debugValues = lib.mkOption {
        type = lib.types.anything;
      };
      config.packages = rec {
        ghc = pkgs.ghcWithPackages (p: with p; [ ieee754 ]);
        inherit (inputs.onelab.packages.${system}) _1lab Agda agda2-mode;
        agda-base = inputs.onelab.packages.${system}.agda;
        agda = agda-base.withPackages (ps: [
          inputs.onelab.packages.${system}._1lab
        ]);
        just-agda = inputs.just-agda.packages.${pkgs.system}.default.override {
          inherit agda agda2-mode;
        };
      };
    };
}
