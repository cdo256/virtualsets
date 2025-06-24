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
          inputs._1lab.packages.${system}._1lab
        ]);
        inherit (inputs._1lab.packages.${system}) _1lab;
        #inherit (pkgs.agdaPackages) _1lab;
        inherit (pkgs.labHaskellPackages) Agda;
        just-agda = inputs.just-agda.packages.${pkgs.system}.default.override { inherit agda; };
      };
    };
}
