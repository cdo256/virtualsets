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
            (import "${self}/support/nix/haskell-packages.nix" { flake = self; })
            (import "${self}/support/nix/agda-overlay.nix" { flake = self; })
          ];
        };
      };
    };
}
