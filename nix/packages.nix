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
        agda = pkgs.agda.withPackages (ps: [
          inputs.onelab.packages.${system}._1lab
          #pkgs.agdaPackages.standard-library
        ]);
        inherit (inputs.onelab.packages.${system}) _1lab;
        #inherit (pkgs.agdaPackages) _1lab;
        inherit (pkgs.labHaskellPackages) Agda;
        inherit (pkgs.emacsPackages) agda2-mode;
        just-agda = inputs.just-agda.packages.${pkgs.system}.default.override {
          inherit agda agda2-mode;
        };
      };
    };
}
