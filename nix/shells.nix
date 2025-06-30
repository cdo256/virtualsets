{ self, inputs, ... }:
{
  perSystem =
    {
      self',
      system,
      pkgs,
      ...
    }:
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with self'.packages; [
          agda
          just-agda
        ];
        shellHook = ''
          ln -sf ${self'.packages.agda-base}/bin/agda $out/bin/agda-base
        '';
      };
    };
}
