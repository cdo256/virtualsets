{ self, inputs, ... }:
{
  systems = [
    "x86_64-linux"
  ];
  perSystem =
    { system, ... }:
    {
      _module.args = {
        pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [
            (import ./haskell-packages.nix { flake = self; })
            (import ./agda-overlay.nix { flake = self; })
          ];
        };
      };
    };
}
