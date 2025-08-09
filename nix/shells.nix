{
  perSystem =
    { self', pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with self'.packages; [
          agda
          just-agda
          (pkgs.python312.withPackages (p: [
            p.matplotlib
          ]))
        ];
      };
    };
}
