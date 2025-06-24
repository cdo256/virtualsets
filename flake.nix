{
  description = "MSc Project on Virtual Sets";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    #nixpkgs.url = "/home/cdo/src/nixpkgs";
    nixpkgs.url = "github:nixos/nixpkgs";
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
      imports = [
        ./nix/args.nix
        ./nix/packages.nix
        ./nix/shells.nix
      ];
    });
}
