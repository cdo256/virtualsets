{
  description = "MSc Project on Virtual Sets";

  inputs = {
    nixpkgs.url = "/home/cdo/src/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    just-agda.url = "github:cdo256/just-agda";
    _1lab.url = "/home/cdo/src/1lab";
    # _1lab.url = "github:cdo256/1lab";
  };

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } (top: {
      systems = [
        "x86_64-linux"
      ];
      perSystem =
        { system, pkgs, ... }:
        let
          agda = pkgs.agda.withPackages (ps: [
            inputs._1lab.packages.${system}.default
            #ps.standard-library
            #ps.agda-categories
          ]);
          just-agda-base = inputs.just-agda.packages.${pkgs.system}.default;
          just-agda = just-agda-base.override { inherit agda; };
        in
        {
          packages = {
            inherit agda just-agda;
            default = just-agda;
          };
          devShells.default = pkgs.mkShell {
            buildInputs = [
              agda
              just-agda
            ];
          };
        };
    });
}
