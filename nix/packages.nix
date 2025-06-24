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
          inputs._1lab.packages.${system}.default
        ]);
        inherit (pkgs.agdaPackages) _1lab;
        inherit (pkgs.labHaskellPackages) Agda;
        just-agda-base = inputs.just-agda.packages.${pkgs.system}.default;
        just-agda = just-agda-base.override { inherit agda; };
      };
    };
}
